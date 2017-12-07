import { Function } from 'core-js/library/web/timers';

"use strict";

var fs = require('fs'),
    tls = require('tls'),
    zlib = require('zlib'),
    Socket = require('net').Socket,
    EventEmitter = require('events').EventEmitter,
    inherits = require('util').inherits,
    inspect = require('util').inspect,
    StringDecoder = require('string_decoder').StringDecoder;

var _ = require("lodash");
var U = require("glace-utils");

var Parser = require('./parser');
var XRegExp = require('xregexp').XRegExp;

var REX_TIMEVAL = XRegExp.cache('^(?<year>\\d{4})(?<month>\\d{2})(?<date>\\d{2})(?<hour>\\d{2})(?<minute>\\d{2})(?<second>\\d+)(?:.\\d+)?$'),
    RE_PASV = /([\d]+),([\d]+),([\d]+),([\d]+),([-\d]+),([-\d]+)/,
    RE_EOL = /\r?\n/g,
    RE_WD = /"(.+)"(?: |$)/,
    RE_SYST = /^([^ ]+)(?: |$)/;
/**
 * Error codes
 *
 * 421: 'Service not available, closing control connection',
 * 425: 'Can\'t open data connection',
 * 426: 'Connection closed; transfer aborted',
 * 450: 'Requested file action not taken / File unavailable (e.g., file busy)',
 * 451: 'Requested action aborted: local error in processing',
 * 452: 'Requested action not taken / Insufficient storage space in system',
 * 500: 'Syntax error / Command unrecognized',
 * 501: 'Syntax error in parameters or arguments',
 * 502: 'Command not implemented',
 * 503: 'Bad sequence of commands',
 * 504: 'Command not implemented for that parameter',
 * 530: 'Not logged in',
 * 532: 'Need account for storing files',
 * 550: 'Requested action not taken / File unavailable (e.g., file not found, no access)',
 * 551: 'Requested action aborted: page type unknown',
 * 552: 'Requested file action aborted / Exceeded storage allocation (for current directory or dataset)',
 * 553: 'Requested action not taken / File name not allowed'
 */
var RETVAL = {
    PRELIM: 1,
    OK: 2,
    WAITING: 3,
    ERR_TEMP: 4,
    ERR_PERM: 5
};
/**
 * Creates new instance of FTP client.
 * 
 * @class
 * @classdesc FTP client with reconnection to provide HA.
 * @arg {object} [opts] - Client options.
 * @arg {string} [opts.host=localhost] - FTP server host.
 * @arg {number} [opts.port=21] - FTP server port.
 * @arg {string} [opts.user=anonymous] - FTP user name.
 * @arg {string} [opts.password=""] - FTP user password.
 * @arg {boolean|string} [opts.secure=false] - Flag to use secure connection.
 * @arg {object} [opts.secureOptions] - Secure connection options to be passed
 *  to `tls.connect`.
 * @arg {number} [opts.pingTime=10000] - Time to ping FTP server, ms.
 * @arg {number} [opts.pollTime=100] - Time to poll tasks queue, ms.
 * @arg {number} [opts.socketTimeout=0] - Socket timeout, disabled by default.
 * @arg {number} [opts.reconnect=Infinity] - Number to reconnect broken connection.
 * @arg {boolean} [opts.keepAlive=true] - Flag to use keep-alive socket
 *  connection.
 */
var Ftp = function (opts) {
  
    this._host = U.defVal(opts.host, "localhost");
    this._port = U.defVal(opts.port, 21);
    this._user = U.defVal(opts.user, "anonymous");
    this._pswd = U.defVal(opts.password, "");
    this._secure = U.defVal(opts.secure, false);
    this._secOpts = U.defVal(opts.secureOptions, {});
    this._pingTime = U.defVal(opts.pingTime, 10000);
    this._pollTime = U.defVal(opts.pollTime, 100);
    this._sockTimeout = U.defVal(opts.socketTimeout, 0);
    this._reconn = U.defVal(opts.reconnect, Infinity);
    this._keepAlive = U.defVal(opts.keepAlive, true);

    this._state = Ftp.STARTED;
    this._tasks = [];
    this._connTasks = [];
    this._connTask = null;
    this._currTask = null;
    this._noopTask = null;
    this._sockErr = null;

    this.on("failed", err => {
        if (this._reconn > 0) {
            this._reconn--;
            this.connect();
        } else {
            this.emit("error", err);
        };
    });
};
inherits(Ftp, EventEmitter);
/* Client states. */
Ftp.INITED = "inited";
Ftp.CONNECTING = "connecting";
Ftp.CONNECTED = "connected";
Ftp.EXECUTING = "executing";
Ftp.EXECUTED = "executed";
Ftp.FAILED = "failed";
Ftp.CLOSED = "closed";
/**
 * Connects to FTP server.
 *
 * @method
 */
Ftp.prototype.connect = function () {
    if (![ Ftp.INITED, Ftp.FAILED, FTP.CLOSED ].includes(this._state)) return;

    this._reset();

    this._state = Ftp.CONNECTING;

    this._parser = new Parser({ debug: this._log });
    this._parser.on("response", (code, text) => {

        var task = this._connTask || this._currTask || this._noopTask;

        var err = null;
        if ([ RETVAL.ERR_TEMP, RETVAL.ERR_PERM ].includes(code / 100 >> 0)) {
            err = mkErr(code, text);
        };
        task.cb(err, code, text);

        if (this._connTask) this._connTasks.shift();
        if (this._currTask) this._tasks.shift();

        this._currTask = this._connTask = this._noopTask = null;
    });

    this._sock = new Socket();
    this._sock.setTimeout(this._sockTimeout);
    this._sock.setEncoding(this._encoding);

    this._sock.on("data", chunk => {
        this._log("[connection] <", inspect(chunk.toString("binary")));
        this._parser.write(chunk);
    });

    this._sock.on("error", err => {
        this._sockErr = err;
    });

    this._sock.on("end", () => {
        if (!this._sockErr) this.emit("end");
    });

    this._sock.on("close", had_err => {
        if (this._sockErr) {
            this._state = FTP.FAILED;
            this.emit("failed", this._sockErr);
            this._sockErr = null;
        } else {
            this.emit("closed");
        };
    });

    var onconn = () => {
        var cmd;
    
        var reenter = (err, text, code) => {

            if (err && (!cmd ||
                        cmd === "USER" ||
                        cmd === "PASS" ||
                        cmd === "TYPE")) {
                this.emit("error", err);
                return this._sock.end();
            };

            if ((this._secure !== true && cmd === "AUTH TLS" && code !== 234) ||
                                         (cmd === "AUTH SSL" && code !== 334) ||
                                         (cmd === "PBSZ" && code !== 200) ||
                                         (cmd === "PROT" && code !== 200)) {
                this.emit("error", mkErr(code, "Unable to secure connection(s)"));
                return this._sock.end();
            };

            if (!cmd) {

                this.emit("greeting", text);

                if (this._secure && this._secure !== "implicit") {
                    cmd = "AUTH TLS";
                    this._addConnTask(cmd, reenter);
                } else {
                    cmd = "USER";
                    this._addConnTask("USER " + this._user, reenter);
                };

            } else if (cmd === "USER") {

                if (code !== 230) {
                    // password required
                    if (!this._pswd && this._pswd !== "") {
                        this.emit("error", mkErr(code, "Password required"));
                        return this._sock.end();
                    };
                    cmd = "PASS";
                    this._addConnTask("PASS " + this._pswd, reenter);

                } else {
                  // no password required
                  cmd = "PASS";
                  reenter(null, text, code);
                };

            } else if (cmd === "PASS") {

                cmd = "FEAT";
                this._addConnTask(cmd, reenter);

            } else if (cmd === "FEAT") {

                if (!err) this._feat = Parser.parseFeat(text);
                cmd = "TYPE";
                this._addConnTask("TYPE I", reenter);

            } else if (cmd === "TYPE") {

                this._state = Ftp.CONNECTED;
                this.emit("ready");

            } else if (cmd === "PBSZ") {

                cmd = "PROT";
                this._addConnTask("PROT P", reenter);

            } else if (cmd === "PROT") {

                cmd = "USER";
                this._addConnTask("USER " + this._user, reenter);

            } else if (cmd.startsWith("AUTH")) {

                if (cmd === "AUTH TLS" && code !== 234 && code !== 200) {

                    cmd = "AUTH SSL";
                    return this._addConnTask(cmd, reenter);

                } else if (cmd === "AUTH TLS") {

                    this._secstate = "upgraded-tls";

                } else if (cmd === "AUTH SSL") {

                    this._secstate = "upgraded-ssl";

                };

                this._sock.removeAllListeners("data");
                this._sock.removeAllListeners("error");
                this._sock._decoder = null;
                this._secOpts.socket = this._sock;
                delete this._secOpts.session;
                this._sock = tls.connect(this._secOpts, onconnect);
                this._sock.setEncoding("binary");
                this._sock.on("data", ondata);
                this._sock.once("end", onend);
                this._sock.on("error", onerror);
            };
        };

        if (this._secState) {
            if (this._secState === 'upgraded-tls' && this._secure === true) {
                cmd = 'PBSZ';
                this._addConnTask('PBSZ 0', reenter);
            } else {
                cmd = 'USER';
                this._addConnTask('USER ' + this._user, reenter);
            }
        } else {
            self._curReq = { cmd: "", cb: reenter };
        };
    };

    if (this._secure) {
        this._secOpts.host = this._host;
        this._secOpts.socket = this._sock;
    };

    if (this._secure === 'implicit')
        this._sock = tls.connect(this._secOpts, onconn);
    else {
        this._sock.once('connect', onconn);
    };

    this._sock.connect(this._port, this._host);

    this._pollId = setInterval(() => this._exec(), this._pollTime);
};
/**
 * Executes command.
 *
 * @method
 * @protected
 */
Ftp.prototype._exec = function () {

    if ([ Ftp.INITED, Ftp.FAILED ].includes(this._status)) {
        if (this._connTasks.length) {

            this._status = Ftp.EXECUTING;
            this._pingId = clearTimeout(this._pingId);
            this._connTask = this._connTasks[0];
            this._log("[connect] >", this._connTask.cmd);
            this._sock.write(this._connTask.cmd + "\r\n");
        };
    };

    if ([ Ftp.CONNECTED, Ftp.EXECUTED ].includes(this._status)) {
        if (this._tasks.length) {

            this._status = Ftp.EXECUTING;
            this._pingId = clearTimeout(this._pingId);
            this._currTask = this._tasks[0];
            this._log("[request] >", this._currTask.cmd);
            this._sock.write(this._currTask.cmd + "\r\n");

        } else if (!this._pingId) {
            this._pingId = setTimeout(() => {

                this._state = Ftp.EXECUTING;
                this._noopTask = { cmd: "NOOP", cb: () => {
                    this._pingId = clearTimeout(this._pingId);
                }};
                this._log("[ping] > NOOP");
                this._sock.write("NOOP\r\n");

            }, this._connTime);
        };
    };
};
/**
 * Adds connection task.
 *
 * @method
 * @protected
 * @arg {string} cmd - FTP connection command. 
 * @arg {function} cb - Callback.
 */
Ftp.prototype._addConnTask = function (cmd, cb) {
    this._connTasks.push({ cmd: cmd, cb: cb });
};
/**
 * Adds task.
 *
 * @method
 * @protected
 * @arg {string} cmd - FTP command. 
 * @arg {function} cb - Callback.
 */
Ftp.prototype._addTask = function (cmd, cb) {
    this._tasks.push({ cmd: cmd, cb: cb });
};
/**
 * Resets FTP client connection.
 *
 * @method
 * @protected
 */
FTP.prototype._reset = function () {
    this._pollId = clearInterval(this._pollId);
};
/**
 * Ends connection.
 *
 * @method
 */
FTP.prototype.end = function () {
    this._reset();
};
/**
 * Sets the transfer data type to ASCII
 *
 * @method
 * @arg {function} cb - Callback.
 */
FTP.prototype.ascii = function (cb) {
    this._addTask("TYPE A", cb);
};
/**
 * Sets the transfer data type to binary (default on connection).
 *
 * @method
 * @arg {function} cb - Callback.
 */
FTP.prototype.binary = function (cb) {
    this._addTask("TYPE I", cb);
};
/**
 * Aborts the current data transfer.
 *
 * @method
 * @arg {boolean} [now=true] - Flag to call command immediately.
 * @arg {boolean} cb - Callback.
 */
FTP.prototype.abort = function (now, cb) {

    if (now instanceof Function) {
        cb = now;
        now = true;
    };
    if (now) {
      this._tasks = [];
    };
    this._addTask("ABOR", cb);
};
/**
 * Changes the current working directory.
 *
 * @method
 * @arg {string} path - Folder path.
 * @arg {function} cb - Callback.
 */
FTP.prototype.cwd = function (path, cb) {
    this._addTask('CWD ' + path, (err, text, code) => {
        if (err) return cb(err);
        var m = RE_WD.exec(text);
        cb(undefined, m ? m[1] : undefined);
    });
};
/**
 * Deletes a file.
 *
 * @method
 * @arg {string} path - File path.
 * @arg {function} cb - Callback.
 */
FTP.prototype.delete = function (path, cb) {
    this._addTask('DELE ' + path, cb);
};
/**
 * Sends command
 *
 * @method
 * @arg {string} cmd - Command to execute.
 * @arg {function} cb - Callback.
 */
FTP.prototype.site = function (cmd, cb) {
    this._addTask('SITE ' + cmd, cb);
};
/**
 * Retrieves human-readable information about the server's status.
 *
 * @method
 * @arg {function} cb - Callback.
 */
FTP.prototype.status = function (cb) {
    this._addTask('STAT', cb);
};
/**
 * Renames file.
 *
 * @method
 * @arg {string} from - Old file path.
 * @arg {string} to - New file path.
 * @arg {function} cb - Callback.
 */
FTP.prototype.rename = function (from, to, cb) {
    this._addTask('RNFR ' + from, err => {
        if (err) return cb(err);
        this._addTask('RNTO ' + to, cb);
    });
};
/**
 * Logs out the user from the server.
 *
 * @method
 * @arg {function} cb - Callback.
 */
FTP.prototype.logout = function (cb) {
    this._addTask('QUIT', cb);
};
/**
 * Similar to `list`, except the directory is temporarily changed to path
 * to retrieve the directory listing.
 *
 * @method
 * @arg {string} path - Folder path.
 * @arg {boolean} [zcomp=false] - Flag to use compression.
 * @arg {function} cb - Callback.
 */
FTP.prototype.listSafe = function (path, zcomp, cb) {

    if (zcomp instanceof Function) {
        cb = zcomp;
        zcomp = false;
    };

    this.pwd((err, origPath) => {
        if (err) return cb(err);

        this.cwd(path, err => {
            if (err) return cb(err);

            this.list(zcomp, (err, list) => {
                if (err) return this.cwd(origPath, cb);

                this.cwd(origPath, err => {
                    if (err) return cb(err);

                    cb(err, list);
                });
            });
        });
    });
};
/**
 * Retrieves the directory.
 *
 * @method
 * @arg {string} path - Folder path.
 * @arg {boolean} [zcomp=false] - Flag to use compression.
 * @arg {function} cb - Callback.
 */
FTP.prototype.list = function (path, zcomp, cb) {

    if (zcomp instanceof Function) {
        cb = zcomp;
        zcomb = false;
    };

    cmd = "LIST " + path;

    this._pasv((err, sock) => {
        if (err) return cb(err);

        if (self._tasks.length && self._tasks[0].cmd === "ABOR") {
            sock.destroy();
            return cb();
        };

        var buffer = "";
        var source = sock;
        var decoder = new StringDecoder("utf8");

        if (zcomp) {
            source = zlib.createDeflate();
            sock.pipe(source);
        };

        source.on("data", chunk => {
            buffer += decoder.write(chunk);
        });

        source.once("error", err => {
        });

        var ondone = () => {
        };

        var final = () => {
        };

        var sendList = () => {
        };

        if (zcomp) {
            this._addTask("MODE Z", (err, text, code) => {
                if (err) {
                    sock.destroy();
                    return cb(mkErr(code, "Compression not supported"));
                };
                sendList();
            });
        } else {
            sendList();
        };
    });
};
/**
 * Retrieves a file.
 *
 * @method
 * @arg {string} path - File path.
 * @arg {boolean} [zcomp=false] - Flag to use compression.
 * @arg {function} cb - Callback.
 */
FTP.prototype.get = function (path, zcomp, cb) {

    if (zcomp instanceof Function) {
        cb = zcomp;
        zcomp = false;
    };

    this._pasv((err, sock) => {
        if (err) return cb(err);

        /* If next command to abort connection no sense to connect socket */
        if (this._tasks.length && this._tasks[0].cmd === "ABOR") {
            sock.destroy();
            return cb();
        };

        var source = sock;

        if (zcomp) {
            source = zlib.createInflate();
            sock.pipe(source);
        };

        sock.pause();

        var sendRetr = () => {
        };

        if (zcomp) {
            self._addTask("MODE Z", (err, text, code) => {
                if (err) {
                    sock.destroy();
                    return cb(mkErr(code, "Compression not supported"));
                };
                sendRetr();
            });
        } else {
            sendRetr();
        }; 
    });
};
/**
 * Sends data to the server to be stored.
 *
 * @method
 * @arg {string|stream} input - Local file or stream.
 * @arg {string} path - Remote file path.
 * @arg {boolean} [zcomp=false] - Flag to use compression. 
 * @arg {function} cb - Callback.
 */
FTP.prototype.put = function (input, path, zcomp, cb) {
  this._store('STOR ' + path, input, zcomp, cb);
};
/**
 * Appends data to existing file or creates new.
 *
 * @method
 * @arg {string|stream} input - Local file or stream.
 * @arg {string} path - Remote file path.
 * @arg {boolean} [zcomp=false] - Flag to use compression.
 * @arg {function} cb - Callback.
 */
FTP.prototype.append = function (input, path, zcomp, cb) {
  this._store('APPE ' + path, input, zcomp, cb);
};
/**
 * Retrieves the current working directory.
 *
 * @method
 * @arg {function} cb - Callback.
 */
FTP.prototype.pwd = function (cb) { // PWD is optional
  var self = this;
  this._send('PWD', function (err, text, code) {
    if (code === 502) {
      return self.cwd('.', function (cwderr, cwd) {
        if (cwderr)
          return cb(cwderr);
        if (cwd === undefined)
          cb(err);
        else
          cb(undefined, cwd);
      }, true);
    } else if (err)
      return cb(err);
    cb(undefined, RE_WD.exec(text)[1]);
  });
};
/**
 * Changes the working directory to the parent of the current directory.
 *
 * @method
 * @arg {function} cb - Callback.
 */
FTP.prototype.cdup = function (cb) { // CDUP is optional
  var self = this;
  this._send('CDUP', function (err, text, code) {
    if (code === 502)
      self.cwd('..', cb, true);
    else
      cb(err);
  });
};
/**
 * Creates a new directory.
 *
 * @method
 * @arg {string} path - Folder path to create.
 * @arg {boolean} [recursive=false] - Flag to create folders recursively.
 * @arg {function} cb - Callback.
 */
FTP.prototype.mkdir = function (path, recursive, cb) { // MKD is optional
  if (typeof recursive === 'function') {
    cb = recursive;
    recursive = false;
  }
  if (!recursive)
    this._send('MKD ' + path, cb);
  else {
    var self = this, owd, abs, dirs, dirslen, i = -1, searching = true;

    abs = (path[0] === '/');

    var nextDir = function () {
      if (++i === dirslen) {
        // return to original working directory
        return self._send('CWD ' + owd, cb, true);
      }
      if (searching) {
        self._send('CWD ' + dirs[i], function (err, text, code) {
          if (code === 550) {
            searching = false;
            --i;
          } else if (err) {
            // return to original working directory
            return self._send('CWD ' + owd, function () {
              cb(err);
            }, true);
          }
          nextDir();
        }, true);
      } else {
        self._send('MKD ' + dirs[i], function (err, text, code) {
          if (err) {
            // return to original working directory
            return self._send('CWD ' + owd, function () {
              cb(err);
            }, true);
          }
          self._send('CWD ' + dirs[i], nextDir, true);
        }, true);
      }
    };
    this.pwd(function (err, cwd) {
      if (err)
        return cb(err);
      owd = cwd;
      if (abs)
        path = path.substr(1);
      if (path[path.length - 1] === '/')
        path = path.substring(0, path.length - 1);
      dirs = path.split('/');
      dirslen = dirs.length;
      if (abs)
        self._send('CWD /', function (err) {
          if (err)
            return cb(err);
          nextDir();
        }, true);
      else
        nextDir();
    });
  }
};
/**
 * Removes directory.
 *
 * @method
 * @arg {string} path - Folder path to remove.
 * @arg {boolean} [recursive=false] - Flag to remove folders recursively.
 * @arg {function} cb - Callback.
 */
FTP.prototype.rmdir = function (path, recursive, cb) { // RMD is optional
  if (typeof recursive === 'function') {
    cb = recursive;
    recursive = false;
  }
  if (!recursive) {
    return this._send('RMD ' + path, cb);
  }
  
  var self = this;
  this.list(path, function (err, list) {
    if (err) return cb(err);
    var idx = 0;
    
    // this function will be called once per listing entry
    var deleteNextEntry;
    deleteNextEntry = function (err) {
      if (err) return cb(err);
      if (idx >= list.length) {
        if (list[0] && list[0].name === path) {
          return cb(null);
        } else {
          return self.rmdir(path, cb);
        }
      }
      
      var entry = list[idx++];
      
      // get the path to the file
      var subpath = null;
      if (entry.name[0] === '/') {
        // this will be the case when you call deleteRecursively() and pass
        // the path to a plain file
        subpath = entry.name;
      } else {
        if (path[path.length - 1] == '/') {
          subpath = path + entry.name;
        } else {
          subpath = path + '/' + entry.name
        }
      }
      
      // delete the entry (recursively) according to its type
      if (entry.type === 'd') {
        if (entry.name === "." || entry.name === "..") {
          return deleteNextEntry();
        }
        self.rmdir(subpath, true, deleteNextEntry);
      } else {
        self.delete(subpath, deleteNextEntry);
      }
    }
    deleteNextEntry();
  });
};
/**
 * Retrieves the server's operating system.
 *
 * @method
 * @arg {function} cb - Callback.
 */
FTP.prototype.system = function (cb) {
    this._addTask("SYST", (err, text) => {
        if (err) return cb(err);
        cb(null, RE_SYST.exec(text)[1]);
    });
};
/**
 * Retrieves the size.
 *
 * @method
 * @arg {string} path - File path.
 * @arg {function} cb - Callback.
 */
FTP.prototype.size = function (path, cb) {
  var self = this;
  this._send('SIZE ' + path, function (err, text, code) {
    if (code === 502) {
      // Note: this may cause a problem as list() is _appended_ to the queue
      return self.list(path, function (err, list) {
        if (err)
          return cb(err);
        if (list.length === 1)
          cb(undefined, list[0].size);
        else {
          // path could have been a directory and we got a listing of its
          // contents, but here we echo the behavior of the real SIZE and
          // return 'File not found' for directories
          cb(new Error('File not found'));
        }
      }, true);
    } else if (err)
      return cb(err);
    cb(undefined, parseInt(text, 10));
  });
};
/**
 * Retrieves the last modified date and time.
 *
 * @method
 * @arg {string} path - File path.
 * @arg {function} cb - Callback.
 */
FTP.prototype.lastMod = function (path, cb) {
  var self = this;
  this._send('MDTM ' + path, function (err, text, code) {
    if (code === 502) {
      return self.list(path, function (err, list) {
        if (err)
          return cb(err);
        if (list.length === 1)
          cb(undefined, list[0].date);
        else
          cb(new Error('File not found'));
      }, true);
    } else if (err)
      return cb(err);
    var val = XRegExp.exec(text, REX_TIMEVAL), ret;
    if (!val)
      return cb(new Error('Invalid date/time format from server'));
    ret = new Date(val.year + '-' + val.month + '-' + val.date + 'T' + val.hour
                   + ':' + val.minute + ':' + val.second);
    cb(undefined, ret);
  });
};
/**
 * Sets the file byte offset for the next file transfer action.
 *
 * @method
 * @arg {number} offset - Byte offset.
 * @arg {function} cb - Callback.
 */
FTP.prototype.restart = function (offset, cb) {
  this._send('REST ' + offset, cb);
};
/**
 * @arg {function} cb - Callback.
 */
FTP.prototype._pasv = function (cb) {

    var reenter = (err, text) => {
        if (err) return cb(err);

        if (first) {
            var m = RE_PASV.exec(text);
        };

        this._pasvConnect(ip, port, (err, sock) => {
            if (err) {

                if (this._sock && ip !== self._sock.remoteAddress) {
                    ip = self._sock.remoteAddress;
                    return reenter();
                };

                this._addTask("ABOR", () => {
                    cb(err);
                });

                return;
            };
            cb(null, sock);
        });
    };

    this._addTask("PASV", reenter);
};
/**
 * @arg {string} ip - IP.
 * @arg {number} port - Port.
 * @arg {function} cb - Callback.
 */
FTP.prototype._pasvConnect = function (ip, port, cb) {

    var pasvSock = new Socket();
    pasvSock.setTimeout(this._sockTimeout);

    pasvSock.once("connect", () => {
        this._log("[request] PASV socket connected");

        if (this._secure) {
            var secOpts = _.cloneDeep(this._secOpts);
            secOpts.session = this._sock.getSession();
            pasvSock = tls.connect(secOpts);
        };

        pasvSock.setTimeout(this._sockTimeout);
        cb(null, pasvSock);
    });

    pasvSock.once("error", err => {
    });

    pasvSock.once("end", () => {
    });

    pasvSock.once("close", had_err => {
    });

    pasvSock.connect(port, ip);
};
/**
 * @arg {string} cmd - FTP command.
 * @arg {string|stream} input - File path or stream.
 * @arg {boolean} [zcomp=false] - Flag to use compression.
 * @arg {function} cb - Callback.
 */
FTP.prototype._store = function (cmd, input, zcomp, cb) {

    if (zcomp instanceof Function) {
        cb = zcomp;
        zcomp = false;
    };

    this._pasv((err, sock) => {
        if (err) return cb(err);

        if (this._tasks.length && this._tasks[0].cmd === "ABOR") {
            sock.destroy();
            return cb();
        };
    });

    sock.once("error", err => {
    });

    var sendStore = () => {
    };

    if (zcomp) {
        this._send("MODE Z", function (err, text, code) {
            if (err) {
                sock.destroy();
                return cb(mkErr(code, 'Compression not supported'));
            }
            dest = zlib.createDeflate({ level: 8 });
            dest.pipe(sock);
            sendStore();
        }, true);
    } else {
        sendStore();
    };
};
/**
 * Helper to make error.
 *
 * @ignore
 * @function
 * @arg {number} code - Error code.
 * @arg {string} msg - Error message.
 * @return {Error} - Error instance.
 */
var mkErr = (code, text) => {
    var err = new Error(msg);
    err.code = code;
    return err;
};

module.exports = Ftp;
