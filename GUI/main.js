"use strict";
// This object will hold all exports.
var Haste = {};
if(typeof window === 'undefined') window = global;

/* Constructor functions for small ADTs. */
function T0(t){this._=t;}
function T1(t,a){this._=t;this.a=a;}
function T2(t,a,b){this._=t;this.a=a;this.b=b;}
function T3(t,a,b,c){this._=t;this.a=a;this.b=b;this.c=c;}
function T4(t,a,b,c,d){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;}
function T5(t,a,b,c,d,e){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;}
function T6(t,a,b,c,d,e,f){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;this.f=f;}

/* Thunk
   Creates a thunk representing the given closure.
   If the non-updatable flag is undefined, the thunk is updatable.
*/
function T(f, nu) {
    this.f = f;
    if(nu === undefined) {
        this.x = __updatable;
    }
}

/* Hint to optimizer that an imported symbol is strict. */
function __strict(x) {return x}

// A tailcall.
function F(f) {
    this.f = f;
}

// A partially applied function. Invariant: members are never thunks.
function PAP(f, args) {
    this.f = f;
    this.args = args;
    this.arity = f.length - args.length;
}

// "Zero" object; used to avoid creating a whole bunch of new objects
// in the extremely common case of a nil-like data constructor.
var __Z = new T0(0);

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

// Indicates that a closure-creating tail loop isn't done.
var __continue = {};

/* Generic apply.
   Applies a function *or* a partial application object to a list of arguments.
   See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/HaskellExecution/FunctionCalls
   for more information.
*/
function A(f, args) {
    while(true) {
        f = E(f);
        if(f instanceof Function) {
            if(args.length === f.length) {
                return f.apply(null, args);
            } else if(args.length < f.length) {
                return new PAP(f, args);
            } else {
                var f2 = f.apply(null, args.slice(0, f.length));
                args = args.slice(f.length);
                f = B(f2);
            }
        } else if(f instanceof PAP) {
            if(args.length === f.arity) {
                return f.f.apply(null, f.args.concat(args));
            } else if(args.length < f.arity) {
                return new PAP(f.f, f.args.concat(args));
            } else {
                var f2 = f.f.apply(null, f.args.concat(args.slice(0, f.arity)));
                args = args.slice(f.arity);
                f = B(f2);
            }
        } else {
            return f;
        }
    }
}

function A1(f, x) {
    f = E(f);
    if(f instanceof Function) {
        return f.length === 1 ? f(x) : new PAP(f, [x]);
    } else if(f instanceof PAP) {
        return f.arity === 1 ? f.f.apply(null, f.args.concat([x]))
                             : new PAP(f.f, f.args.concat([x]));
    } else {
        return f;
    }
}

function A2(f, x, y) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 2:  return f(x, y);
        case 1:  return A1(B(f(x)), y);
        default: return new PAP(f, [x,y]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 2:  return f.f.apply(null, f.args.concat([x,y]));
        case 1:  return A1(B(f.f.apply(null, f.args.concat([x]))), y);
        default: return new PAP(f.f, f.args.concat([x,y]));
        }
    } else {
        return f;
    }
}

function A3(f, x, y, z) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 3:  return f(x, y, z);
        case 2:  return A1(B(f(x, y)), z);
        case 1:  return A2(B(f(x)), y, z);
        default: return new PAP(f, [x,y,z]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 3:  return f.f.apply(null, f.args.concat([x,y,z]));
        case 2:  return A1(B(f.f.apply(null, f.args.concat([x,y]))), z);
        case 1:  return A2(B(f.f.apply(null, f.args.concat([x]))), y, z);
        default: return new PAP(f.f, f.args.concat([x,y,z]));
        }
    } else {
        return f;
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            if(t.x === __updatable) {
                var f = t.f;
                t.f = __blackhole;
                t.x = f();
            } else {
                return t.f();
            }
        }
        if(t.x === __updatable) {
            throw 'Infinite loop!';
        } else {
            return t.x;
        }
    } else {
        return t;
    }
}

/* Tail call chain counter. */
var C = 0, Cs = [];

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    Cs.push(C);
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        C = 0;
        f = fun();
    }
    C = Cs.pop();
    return f;
}

// Export Haste, A, B and E. Haste because we need to preserve exports, A, B
// and E because they're handy for Haste.Foreign.
if(!window) {
    var window = {};
}
window['Haste'] = Haste;
window['A'] = A;
window['E'] = E;
window['B'] = B;


/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw E(err);
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return {_:0, a:(a-a%b)/b, b:a%b};
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
if(Math.imul) {
    var imul = Math.imul;
} else {
    var imul = function(a, b) {
        // ignore high a * high a as the result will always be truncated
        var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
        var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
        var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
        return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
    }
}

function addC(a, b) {
    var x = a+b;
    return {_:0, a:x & 0xffffffff, b:x > 0x7fffffff};
}

function subC(a, b) {
    var x = a-b;
    return {_:0, a:x & 0xffffffff, b:x < -2147483648};
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

function isFloatFinite(x) {
    return isFinite(x);
}

function isDoubleFinite(x) {
    return isFinite(x);
}

function err(str) {
    die(toJSStr(str));
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, __Z);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = B(A(f, [str.charCodeAt(i), acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return {_:1,a:str.charCodeAt(i),b:new T(function() {
            return unAppCStr(str,chrs,i+1);
        })};
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str._ == 1; str = E(str.b)) {
        s += String.fromCharCode(E(str.a));
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = B(A(f, [mv.x]));
    mv.x = x.a;
    return x.b;
}

function localeEncoding() {
    var le = newByteArr(5);
    le['v']['i8'][0] = 'U'.charCodeAt(0);
    le['v']['i8'][1] = 'T'.charCodeAt(0);
    le['v']['i8'][2] = 'F'.charCodeAt(0);
    le['v']['i8'][3] = '-'.charCodeAt(0);
    le['v']['i8'][4] = '8'.charCodeAt(0);
    return le;
}

var isDoubleNaN = isNaN;
var isFloatNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return 0;
    } else if(a == b) {
        return 1;
    }
    return 2;
}

/* Convert a JS exception into a Haskell JSException */
function __hsException(e) {
  e = e.toString();
  var x = new Long(2904464383, 3929545892, true);
  var y = new Long(3027541338, 3270546716, true);
  var t = new T5(0, x, y
                  , new T5(0, x, y
                            , unCStr("haste-prim")
                            , unCStr("Haste.Prim.Foreign")
                            , unCStr("JSException")), __Z, __Z);
  var show = function(x) {return unCStr(E(x).a);}
  var dispEx = function(x) {return unCStr("JavaScript exception: " + E(x).a);}
  var showList = function(_, s) {return unAppCStr(e, s);}
  var showsPrec = function(_, _p, s) {return unAppCStr(e, s);}
  var showDict = new T3(0, showsPrec, show, showList);
  var self;
  var fromEx = function(_) {return new T1(1, self);}
  var dict = new T5(0, t, showDict, null /* toException */, fromEx, dispEx);
  self = new T2(0, dict, new T1(0, e));
  return self;
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        if(typeof e._ === 'undefined') {
            e = __hsException(e);
        }
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Object) {
        return x._;
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round, rintDouble = jsRound, rintFloat = jsRound;
var jsTrunc = Math.trunc ? Math.trunc : function(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
};
function jsRoundW(n) {
    return Math.abs(jsTrunc(n));
}
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt64(i) {
    return popCnt(i.low) + popCnt(i.high);
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

function __clz(bits, x) {
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    } else {
        return bits - (1 + Math.floor(Math.log(x)/Math.LN2));
    }
}

// TODO: can probably be done much faster with arithmetic tricks like __clz
function __ctz(bits, x) {
    var y = 1;
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    }
    for(var i = 0; i < bits; ++i) {
        if(y & x) {
            return i;
        } else {
            y <<= 1;
        }
    }
    return 0;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    if(x === 0) {
        return __decodedZeroF;
    }
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return {_:0, a:sign*man, b:exp};
}

var __decodedZero = {_:0,a:1,b:0,c:0,d:0};
var __decodedZeroF = {_:0,a:1,b:0};

function decodeDouble(x) {
    if(x === 0) {
        // GHC 7.10+ *really* doesn't like 0 to be represented as anything
        // but zeroes all the way.
        return __decodedZero;
    }
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return {_:0, a:sign, b:manHigh, c:manLow, d:exp};
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

window['jsGetMouseCoords'] = function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = window.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - (e.currentTarget.offsetLeft || 0),
	    posy - (e.currentTarget.offsetTop || 0)];
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs._) {
        strs = E(strs);
        arr.push(E(strs.a));
        strs = E(strs.b);
    }
    return arr.join(sep);
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return __Z;
    }
    return {_:1,a:hs};
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return {_:0, a:jsRead(obj)};
    case 'string':
        return {_:1, a:obj};
    case 'boolean':
        return {_:2, a:obj}; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return {_:3, a:arr2lst_json(obj, 0)};
        } else if (obj == null) {
            return {_:5};
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = {_:1, a:{_:0, a:ks[i], b:toHS(obj[ks[i]])}, b:xs};
            }
            return {_:4, a:xs};
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1, a:toHS(arr[elem]), b:new T(function() {return arr2lst_json(arr,elem+1);}),c:true}
}

/* gettimeofday(2) */
function gettimeofday(tv, _tz) {
    var t = new Date().getTime();
    writeOffAddr("i32", 4, tv, 0, (t/1000)|0);
    writeOffAddr("i32", 4, tv, 1, ((t%1000)*1000)|0);
    return 0;
}

// Create a little endian ArrayBuffer representation of something.
function toABHost(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    return a;
}

function toABSwap(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    var bs = new Uint8Array(a);
    for(var i = 0, j = n-1; i < j; ++i, --j) {
        var tmp = bs[i];
        bs[i] = bs[j];
        bs[j] = tmp;
    }
    return a;
}

window['toABle'] = toABHost;
window['toABbe'] = toABSwap;

// Swap byte order if host is not little endian.
var buffer = new ArrayBuffer(2);
new DataView(buffer).setInt16(0, 256, true);
if(new Int16Array(buffer)[0] !== 256) {
    window['toABle'] = toABSwap;
    window['toABbe'] = toABHost;
}

/* bn.js by Fedor Indutny, see doc/LICENSE.bn for license */
var __bn = {};
(function (module, exports) {
'use strict';

function BN(number, base, endian) {
  // May be `new BN(bn)` ?
  if (number !== null &&
      typeof number === 'object' &&
      Array.isArray(number.words)) {
    return number;
  }

  this.negative = 0;
  this.words = null;
  this.length = 0;

  if (base === 'le' || base === 'be') {
    endian = base;
    base = 10;
  }

  if (number !== null)
    this._init(number || 0, base || 10, endian || 'be');
}
if (typeof module === 'object')
  module.exports = BN;
else
  exports.BN = BN;

BN.BN = BN;
BN.wordSize = 26;

BN.max = function max(left, right) {
  if (left.cmp(right) > 0)
    return left;
  else
    return right;
};

BN.min = function min(left, right) {
  if (left.cmp(right) < 0)
    return left;
  else
    return right;
};

BN.prototype._init = function init(number, base, endian) {
  if (typeof number === 'number') {
    return this._initNumber(number, base, endian);
  } else if (typeof number === 'object') {
    return this._initArray(number, base, endian);
  }
  if (base === 'hex')
    base = 16;

  number = number.toString().replace(/\s+/g, '');
  var start = 0;
  if (number[0] === '-')
    start++;

  if (base === 16)
    this._parseHex(number, start);
  else
    this._parseBase(number, base, start);

  if (number[0] === '-')
    this.negative = 1;

  this.strip();

  if (endian !== 'le')
    return;

  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initNumber = function _initNumber(number, base, endian) {
  if (number < 0) {
    this.negative = 1;
    number = -number;
  }
  if (number < 0x4000000) {
    this.words = [ number & 0x3ffffff ];
    this.length = 1;
  } else if (number < 0x10000000000000) {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff
    ];
    this.length = 2;
  } else {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff,
      1
    ];
    this.length = 3;
  }

  if (endian !== 'le')
    return;

  // Reverse the bytes
  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initArray = function _initArray(number, base, endian) {
  if (number.length <= 0) {
    this.words = [ 0 ];
    this.length = 1;
    return this;
  }

  this.length = Math.ceil(number.length / 3);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  var off = 0;
  if (endian === 'be') {
    for (var i = number.length - 1, j = 0; i >= 0; i -= 3) {
      var w = number[i] | (number[i - 1] << 8) | (number[i - 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  } else if (endian === 'le') {
    for (var i = 0, j = 0; i < number.length; i += 3) {
      var w = number[i] | (number[i + 1] << 8) | (number[i + 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  }
  return this.strip();
};

function parseHex(str, start, end) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r <<= 4;

    // 'a' - 'f'
    if (c >= 49 && c <= 54)
      r |= c - 49 + 0xa;

    // 'A' - 'F'
    else if (c >= 17 && c <= 22)
      r |= c - 17 + 0xa;

    // '0' - '9'
    else
      r |= c & 0xf;
  }
  return r;
}

BN.prototype._parseHex = function _parseHex(number, start) {
  // Create possibly bigger array to ensure that it fits the number
  this.length = Math.ceil((number.length - start) / 6);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  // Scan 24-bit chunks and add them to the number
  var off = 0;
  for (var i = number.length - 6, j = 0; i >= start; i -= 6) {
    var w = parseHex(number, i, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
    off += 24;
    if (off >= 26) {
      off -= 26;
      j++;
    }
  }
  if (i + 6 !== start) {
    var w = parseHex(number, start, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
  }
  this.strip();
};

function parseBase(str, start, end, mul) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r *= mul;

    // 'a'
    if (c >= 49)
      r += c - 49 + 0xa;

    // 'A'
    else if (c >= 17)
      r += c - 17 + 0xa;

    // '0' - '9'
    else
      r += c;
  }
  return r;
}

BN.prototype._parseBase = function _parseBase(number, base, start) {
  // Initialize as zero
  this.words = [ 0 ];
  this.length = 1;

  // Find length of limb in base
  for (var limbLen = 0, limbPow = 1; limbPow <= 0x3ffffff; limbPow *= base)
    limbLen++;
  limbLen--;
  limbPow = (limbPow / base) | 0;

  var total = number.length - start;
  var mod = total % limbLen;
  var end = Math.min(total, total - mod) + start;

  var word = 0;
  for (var i = start; i < end; i += limbLen) {
    word = parseBase(number, i, i + limbLen, base);

    this.imuln(limbPow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }

  if (mod !== 0) {
    var pow = 1;
    var word = parseBase(number, i, number.length, base);

    for (var i = 0; i < mod; i++)
      pow *= base;
    this.imuln(pow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }
};

BN.prototype.copy = function copy(dest) {
  dest.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    dest.words[i] = this.words[i];
  dest.length = this.length;
  dest.negative = this.negative;
};

BN.prototype.clone = function clone() {
  var r = new BN(null);
  this.copy(r);
  return r;
};

// Remove leading `0` from `this`
BN.prototype.strip = function strip() {
  while (this.length > 1 && this.words[this.length - 1] === 0)
    this.length--;
  return this._normSign();
};

BN.prototype._normSign = function _normSign() {
  // -0 = 0
  if (this.length === 1 && this.words[0] === 0)
    this.negative = 0;
  return this;
};

var zeros = [
  '',
  '0',
  '00',
  '000',
  '0000',
  '00000',
  '000000',
  '0000000',
  '00000000',
  '000000000',
  '0000000000',
  '00000000000',
  '000000000000',
  '0000000000000',
  '00000000000000',
  '000000000000000',
  '0000000000000000',
  '00000000000000000',
  '000000000000000000',
  '0000000000000000000',
  '00000000000000000000',
  '000000000000000000000',
  '0000000000000000000000',
  '00000000000000000000000',
  '000000000000000000000000',
  '0000000000000000000000000'
];

var groupSizes = [
  0, 0,
  25, 16, 12, 11, 10, 9, 8,
  8, 7, 7, 7, 7, 6, 6,
  6, 6, 6, 6, 6, 5, 5,
  5, 5, 5, 5, 5, 5, 5,
  5, 5, 5, 5, 5, 5, 5
];

var groupBases = [
  0, 0,
  33554432, 43046721, 16777216, 48828125, 60466176, 40353607, 16777216,
  43046721, 10000000, 19487171, 35831808, 62748517, 7529536, 11390625,
  16777216, 24137569, 34012224, 47045881, 64000000, 4084101, 5153632,
  6436343, 7962624, 9765625, 11881376, 14348907, 17210368, 20511149,
  24300000, 28629151, 33554432, 39135393, 45435424, 52521875, 60466176
];

BN.prototype.toString = function toString(base, padding) {
  base = base || 10;
  var padding = padding | 0 || 1;
  if (base === 16 || base === 'hex') {
    var out = '';
    var off = 0;
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var w = this.words[i];
      var word = (((w << off) | carry) & 0xffffff).toString(16);
      carry = (w >>> (24 - off)) & 0xffffff;
      if (carry !== 0 || i !== this.length - 1)
        out = zeros[6 - word.length] + word + out;
      else
        out = word + out;
      off += 2;
      if (off >= 26) {
        off -= 26;
        i--;
      }
    }
    if (carry !== 0)
      out = carry.toString(16) + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else if (base === (base | 0) && base >= 2 && base <= 36) {
    var groupSize = groupSizes[base];
    var groupBase = groupBases[base];
    var out = '';
    var c = this.clone();
    c.negative = 0;
    while (c.cmpn(0) !== 0) {
      var r = c.modn(groupBase).toString(base);
      c = c.idivn(groupBase);

      if (c.cmpn(0) !== 0)
        out = zeros[groupSize - r.length] + r + out;
      else
        out = r + out;
    }
    if (this.cmpn(0) === 0)
      out = '0' + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else {
    throw 'Base should be between 2 and 36';
  }
};

BN.prototype.toJSON = function toJSON() {
  return this.toString(16);
};

BN.prototype.toArray = function toArray(endian, length) {
  this.strip();
  var littleEndian = endian === 'le';
  var res = new Array(this.byteLength());
  res[0] = 0;

  var q = this.clone();
  if (!littleEndian) {
    // Assume big-endian
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[res.length - i - 1] = b;
    }
  } else {
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[i] = b;
    }
  }

  if (length) {
    while (res.length < length) {
      if (littleEndian)
        res.push(0);
      else
        res.unshift(0);
    }
  }

  return res;
};

if (Math.clz32) {
  BN.prototype._countBits = function _countBits(w) {
    return 32 - Math.clz32(w);
  };
} else {
  BN.prototype._countBits = function _countBits(w) {
    var t = w;
    var r = 0;
    if (t >= 0x1000) {
      r += 13;
      t >>>= 13;
    }
    if (t >= 0x40) {
      r += 7;
      t >>>= 7;
    }
    if (t >= 0x8) {
      r += 4;
      t >>>= 4;
    }
    if (t >= 0x02) {
      r += 2;
      t >>>= 2;
    }
    return r + t;
  };
}

// Return number of used bits in a BN
BN.prototype.bitLength = function bitLength() {
  var hi = 0;
  var w = this.words[this.length - 1];
  var hi = this._countBits(w);
  return (this.length - 1) * 26 + hi;
};

BN.prototype.byteLength = function byteLength() {
  return Math.ceil(this.bitLength() / 8);
};

// Return negative clone of `this`
BN.prototype.neg = function neg() {
  if (this.cmpn(0) === 0)
    return this.clone();

  var r = this.clone();
  r.negative = this.negative ^ 1;
  return r;
};

BN.prototype.ineg = function ineg() {
  this.negative ^= 1;
  return this;
};

// Or `num` with `this` in-place
BN.prototype.iuor = function iuor(num) {
  while (this.length < num.length)
    this.words[this.length++] = 0;

  for (var i = 0; i < num.length; i++)
    this.words[i] = this.words[i] | num.words[i];

  return this.strip();
};

BN.prototype.ior = function ior(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuor(num);
};


// Or `num` with `this`
BN.prototype.or = function or(num) {
  if (this.length > num.length)
    return this.clone().ior(num);
  else
    return num.clone().ior(this);
};

BN.prototype.uor = function uor(num) {
  if (this.length > num.length)
    return this.clone().iuor(num);
  else
    return num.clone().iuor(this);
};


// And `num` with `this` in-place
BN.prototype.iuand = function iuand(num) {
  // b = min-length(num, this)
  var b;
  if (this.length > num.length)
    b = num;
  else
    b = this;

  for (var i = 0; i < b.length; i++)
    this.words[i] = this.words[i] & num.words[i];

  this.length = b.length;

  return this.strip();
};

BN.prototype.iand = function iand(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuand(num);
};


// And `num` with `this`
BN.prototype.and = function and(num) {
  if (this.length > num.length)
    return this.clone().iand(num);
  else
    return num.clone().iand(this);
};

BN.prototype.uand = function uand(num) {
  if (this.length > num.length)
    return this.clone().iuand(num);
  else
    return num.clone().iuand(this);
};


// Xor `num` with `this` in-place
BN.prototype.iuxor = function iuxor(num) {
  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  for (var i = 0; i < b.length; i++)
    this.words[i] = a.words[i] ^ b.words[i];

  if (this !== a)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];

  this.length = a.length;

  return this.strip();
};

BN.prototype.ixor = function ixor(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuxor(num);
};


// Xor `num` with `this`
BN.prototype.xor = function xor(num) {
  if (this.length > num.length)
    return this.clone().ixor(num);
  else
    return num.clone().ixor(this);
};

BN.prototype.uxor = function uxor(num) {
  if (this.length > num.length)
    return this.clone().iuxor(num);
  else
    return num.clone().iuxor(this);
};


// Add `num` to `this` in-place
BN.prototype.iadd = function iadd(num) {
  // negative + positive
  if (this.negative !== 0 && num.negative === 0) {
    this.negative = 0;
    var r = this.isub(num);
    this.negative ^= 1;
    return this._normSign();

  // positive + negative
  } else if (this.negative === 0 && num.negative !== 0) {
    num.negative = 0;
    var r = this.isub(num);
    num.negative = 1;
    return r._normSign();
  }

  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) + (b.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }

  this.length = a.length;
  if (carry !== 0) {
    this.words[this.length] = carry;
    this.length++;
  // Copy the rest of the words
  } else if (a !== this) {
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  }

  return this;
};

// Add `num` to `this`
BN.prototype.add = function add(num) {
  if (num.negative !== 0 && this.negative === 0) {
    num.negative = 0;
    var res = this.sub(num);
    num.negative ^= 1;
    return res;
  } else if (num.negative === 0 && this.negative !== 0) {
    this.negative = 0;
    var res = num.sub(this);
    this.negative = 1;
    return res;
  }

  if (this.length > num.length)
    return this.clone().iadd(num);
  else
    return num.clone().iadd(this);
};

// Subtract `num` from `this` in-place
BN.prototype.isub = function isub(num) {
  // this - (-num) = this + num
  if (num.negative !== 0) {
    num.negative = 0;
    var r = this.iadd(num);
    num.negative = 1;
    return r._normSign();

  // -this - num = -(this + num)
  } else if (this.negative !== 0) {
    this.negative = 0;
    this.iadd(num);
    this.negative = 1;
    return this._normSign();
  }

  // At this point both numbers are positive
  var cmp = this.cmp(num);

  // Optimization - zeroify
  if (cmp === 0) {
    this.negative = 0;
    this.length = 1;
    this.words[0] = 0;
    return this;
  }

  // a > b
  var a;
  var b;
  if (cmp > 0) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) - (b.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }

  // Copy rest of the words
  if (carry === 0 && i < a.length && a !== this)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  this.length = Math.max(this.length, i);

  if (a !== this)
    this.negative = 1;

  return this.strip();
};

// Subtract `num` from `this`
BN.prototype.sub = function sub(num) {
  return this.clone().isub(num);
};

function smallMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  var len = (self.length + num.length) | 0;
  out.length = len;
  len = (len - 1) | 0;

  // Peel one iteration (compiler can't do it, because of code complexity)
  var a = self.words[0] | 0;
  var b = num.words[0] | 0;
  var r = a * b;

  var lo = r & 0x3ffffff;
  var carry = (r / 0x4000000) | 0;
  out.words[0] = lo;

  for (var k = 1; k < len; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = carry >>> 26;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = (k - j) | 0;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;
    }
    out.words[k] = rword | 0;
    carry = ncarry | 0;
  }
  if (carry !== 0) {
    out.words[k] = carry | 0;
  } else {
    out.length--;
  }

  return out.strip();
}

function bigMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  out.length = self.length + num.length;

  var carry = 0;
  var hncarry = 0;
  for (var k = 0; k < out.length - 1; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = hncarry;
    hncarry = 0;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;

      hncarry += ncarry >>> 26;
      ncarry &= 0x3ffffff;
    }
    out.words[k] = rword;
    carry = ncarry;
    ncarry = hncarry;
  }
  if (carry !== 0) {
    out.words[k] = carry;
  } else {
    out.length--;
  }

  return out.strip();
}

BN.prototype.mulTo = function mulTo(num, out) {
  var res;
  if (this.length + num.length < 63)
    res = smallMulTo(this, num, out);
  else
    res = bigMulTo(this, num, out);
  return res;
};

// Multiply `this` by `num`
BN.prototype.mul = function mul(num) {
  var out = new BN(null);
  out.words = new Array(this.length + num.length);
  return this.mulTo(num, out);
};

// In-place Multiplication
BN.prototype.imul = function imul(num) {
  if (this.cmpn(0) === 0 || num.cmpn(0) === 0) {
    this.words[0] = 0;
    this.length = 1;
    return this;
  }

  var tlen = this.length;
  var nlen = num.length;

  this.negative = num.negative ^ this.negative;
  this.length = this.length + num.length;
  this.words[this.length - 1] = 0;

  for (var k = this.length - 2; k >= 0; k--) {
    // Sum all words with the same `i + j = k` and accumulate `carry`,
    // note that carry could be >= 0x3ffffff
    var carry = 0;
    var rword = 0;
    var maxJ = Math.min(k, nlen - 1);
    for (var j = Math.max(0, k - tlen + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = this.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      carry += (r / 0x4000000) | 0;
      lo += rword;
      rword = lo & 0x3ffffff;
      carry += lo >>> 26;
    }
    this.words[k] = rword;
    this.words[k + 1] += carry;
    carry = 0;
  }

  // Propagate overflows
  var carry = 0;
  for (var i = 1; i < this.length; i++) {
    var w = (this.words[i] | 0) + carry;
    this.words[i] = w & 0x3ffffff;
    carry = w >>> 26;
  }

  return this.strip();
};

BN.prototype.imuln = function imuln(num) {
  // Carry
  var carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = (this.words[i] | 0) * num;
    var lo = (w & 0x3ffffff) + (carry & 0x3ffffff);
    carry >>= 26;
    carry += (w / 0x4000000) | 0;
    // NOTE: lo is 27bit maximum
    carry += lo >>> 26;
    this.words[i] = lo & 0x3ffffff;
  }

  if (carry !== 0) {
    this.words[i] = carry;
    this.length++;
  }

  return this;
};

BN.prototype.muln = function muln(num) {
  return this.clone().imuln(num);
};

// `this` * `this`
BN.prototype.sqr = function sqr() {
  return this.mul(this);
};

// `this` * `this` in-place
BN.prototype.isqr = function isqr() {
  return this.mul(this);
};

// Shift-left in-place
BN.prototype.iushln = function iushln(bits) {
  var r = bits % 26;
  var s = (bits - r) / 26;
  var carryMask = (0x3ffffff >>> (26 - r)) << (26 - r);

  if (r !== 0) {
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var newCarry = this.words[i] & carryMask;
      var c = ((this.words[i] | 0) - newCarry) << r;
      this.words[i] = c | carry;
      carry = newCarry >>> (26 - r);
    }
    if (carry) {
      this.words[i] = carry;
      this.length++;
    }
  }

  if (s !== 0) {
    for (var i = this.length - 1; i >= 0; i--)
      this.words[i + s] = this.words[i];
    for (var i = 0; i < s; i++)
      this.words[i] = 0;
    this.length += s;
  }

  return this.strip();
};

BN.prototype.ishln = function ishln(bits) {
  return this.iushln(bits);
};

// Shift-right in-place
BN.prototype.iushrn = function iushrn(bits, hint, extended) {
  var h;
  if (hint)
    h = (hint - (hint % 26)) / 26;
  else
    h = 0;

  var r = bits % 26;
  var s = Math.min((bits - r) / 26, this.length);
  var mask = 0x3ffffff ^ ((0x3ffffff >>> r) << r);
  var maskedWords = extended;

  h -= s;
  h = Math.max(0, h);

  // Extended mode, copy masked part
  if (maskedWords) {
    for (var i = 0; i < s; i++)
      maskedWords.words[i] = this.words[i];
    maskedWords.length = s;
  }

  if (s === 0) {
    // No-op, we should not move anything at all
  } else if (this.length > s) {
    this.length -= s;
    for (var i = 0; i < this.length; i++)
      this.words[i] = this.words[i + s];
  } else {
    this.words[0] = 0;
    this.length = 1;
  }

  var carry = 0;
  for (var i = this.length - 1; i >= 0 && (carry !== 0 || i >= h); i--) {
    var word = this.words[i] | 0;
    this.words[i] = (carry << (26 - r)) | (word >>> r);
    carry = word & mask;
  }

  // Push carried bits as a mask
  if (maskedWords && carry !== 0)
    maskedWords.words[maskedWords.length++] = carry;

  if (this.length === 0) {
    this.words[0] = 0;
    this.length = 1;
  }

  this.strip();

  return this;
};

BN.prototype.ishrn = function ishrn(bits, hint, extended) {
  return this.iushrn(bits, hint, extended);
};

// Shift-left
BN.prototype.shln = function shln(bits) {
  var x = this.clone();
  var neg = x.negative;
  x.negative = false;
  x.ishln(bits);
  x.negative = neg;
  return x;
};

BN.prototype.ushln = function ushln(bits) {
  return this.clone().iushln(bits);
};

// Shift-right
BN.prototype.shrn = function shrn(bits) {
  var x = this.clone();
  if(x.negative) {
      x.negative = false;
      x.ishrn(bits);
      x.negative = true;
      return x.isubn(1);
  } else {
      return x.ishrn(bits);
  }
};

BN.prototype.ushrn = function ushrn(bits) {
  return this.clone().iushrn(bits);
};

// Test if n bit is set
BN.prototype.testn = function testn(bit) {
  var r = bit % 26;
  var s = (bit - r) / 26;
  var q = 1 << r;

  // Fast case: bit is much higher than all existing words
  if (this.length <= s) {
    return false;
  }

  // Check bit and return
  var w = this.words[s];

  return !!(w & q);
};

// Add plain number `num` to `this`
BN.prototype.iaddn = function iaddn(num) {
  if (num < 0)
    return this.isubn(-num);

  // Possible sign change
  if (this.negative !== 0) {
    if (this.length === 1 && (this.words[0] | 0) < num) {
      this.words[0] = num - (this.words[0] | 0);
      this.negative = 0;
      return this;
    }

    this.negative = 0;
    this.isubn(num);
    this.negative = 1;
    return this;
  }

  // Add without checks
  return this._iaddn(num);
};

BN.prototype._iaddn = function _iaddn(num) {
  this.words[0] += num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] >= 0x4000000; i++) {
    this.words[i] -= 0x4000000;
    if (i === this.length - 1)
      this.words[i + 1] = 1;
    else
      this.words[i + 1]++;
  }
  this.length = Math.max(this.length, i + 1);

  return this;
};

// Subtract plain number `num` from `this`
BN.prototype.isubn = function isubn(num) {
  if (num < 0)
    return this.iaddn(-num);

  if (this.negative !== 0) {
    this.negative = 0;
    this.iaddn(num);
    this.negative = 1;
    return this;
  }

  this.words[0] -= num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] < 0; i++) {
    this.words[i] += 0x4000000;
    this.words[i + 1] -= 1;
  }

  return this.strip();
};

BN.prototype.addn = function addn(num) {
  return this.clone().iaddn(num);
};

BN.prototype.subn = function subn(num) {
  return this.clone().isubn(num);
};

BN.prototype.iabs = function iabs() {
  this.negative = 0;

  return this;
};

BN.prototype.abs = function abs() {
  return this.clone().iabs();
};

BN.prototype._ishlnsubmul = function _ishlnsubmul(num, mul, shift) {
  // Bigger storage is needed
  var len = num.length + shift;
  var i;
  if (this.words.length < len) {
    var t = new Array(len);
    for (var i = 0; i < this.length; i++)
      t[i] = this.words[i];
    this.words = t;
  } else {
    i = this.length;
  }

  // Zeroify rest
  this.length = Math.max(this.length, len);
  for (; i < this.length; i++)
    this.words[i] = 0;

  var carry = 0;
  for (var i = 0; i < num.length; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    var right = (num.words[i] | 0) * mul;
    w -= right & 0x3ffffff;
    carry = (w >> 26) - ((right / 0x4000000) | 0);
    this.words[i + shift] = w & 0x3ffffff;
  }
  for (; i < this.length - shift; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    carry = w >> 26;
    this.words[i + shift] = w & 0x3ffffff;
  }

  if (carry === 0)
    return this.strip();

  carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = -(this.words[i] | 0) + carry;
    carry = w >> 26;
    this.words[i] = w & 0x3ffffff;
  }
  this.negative = 1;

  return this.strip();
};

BN.prototype._wordDiv = function _wordDiv(num, mode) {
  var shift = this.length - num.length;

  var a = this.clone();
  var b = num;

  // Normalize
  var bhi = b.words[b.length - 1] | 0;
  var bhiBits = this._countBits(bhi);
  shift = 26 - bhiBits;
  if (shift !== 0) {
    b = b.ushln(shift);
    a.iushln(shift);
    bhi = b.words[b.length - 1] | 0;
  }

  // Initialize quotient
  var m = a.length - b.length;
  var q;

  if (mode !== 'mod') {
    q = new BN(null);
    q.length = m + 1;
    q.words = new Array(q.length);
    for (var i = 0; i < q.length; i++)
      q.words[i] = 0;
  }

  var diff = a.clone()._ishlnsubmul(b, 1, m);
  if (diff.negative === 0) {
    a = diff;
    if (q)
      q.words[m] = 1;
  }

  for (var j = m - 1; j >= 0; j--) {
    var qj = (a.words[b.length + j] | 0) * 0x4000000 +
             (a.words[b.length + j - 1] | 0);

    // NOTE: (qj / bhi) is (0x3ffffff * 0x4000000 + 0x3ffffff) / 0x2000000 max
    // (0x7ffffff)
    qj = Math.min((qj / bhi) | 0, 0x3ffffff);

    a._ishlnsubmul(b, qj, j);
    while (a.negative !== 0) {
      qj--;
      a.negative = 0;
      a._ishlnsubmul(b, 1, j);
      if (a.cmpn(0) !== 0)
        a.negative ^= 1;
    }
    if (q)
      q.words[j] = qj;
  }
  if (q)
    q.strip();
  a.strip();

  // Denormalize
  if (mode !== 'div' && shift !== 0)
    a.iushrn(shift);
  return { div: q ? q : null, mod: a };
};

BN.prototype.divmod = function divmod(num, mode, positive) {
  if (this.negative !== 0 && num.negative === 0) {
    var res = this.neg().divmod(num, mode);
    var div;
    var mod;
    if (mode !== 'mod')
      div = res.div.neg();
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.add(num);
    }
    return {
      div: div,
      mod: mod
    };
  } else if (this.negative === 0 && num.negative !== 0) {
    var res = this.divmod(num.neg(), mode);
    var div;
    if (mode !== 'mod')
      div = res.div.neg();
    return { div: div, mod: res.mod };
  } else if ((this.negative & num.negative) !== 0) {
    var res = this.neg().divmod(num.neg(), mode);
    var mod;
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.isub(num);
    }
    return {
      div: res.div,
      mod: mod
    };
  }

  // Both numbers are positive at this point

  // Strip both numbers to approximate shift value
  if (num.length > this.length || this.cmp(num) < 0)
    return { div: new BN(0), mod: this };

  // Very short reduction
  if (num.length === 1) {
    if (mode === 'div')
      return { div: this.divn(num.words[0]), mod: null };
    else if (mode === 'mod')
      return { div: null, mod: new BN(this.modn(num.words[0])) };
    return {
      div: this.divn(num.words[0]),
      mod: new BN(this.modn(num.words[0]))
    };
  }

  return this._wordDiv(num, mode);
};

// Find `this` / `num`
BN.prototype.div = function div(num) {
  return this.divmod(num, 'div', false).div;
};

// Find `this` % `num`
BN.prototype.mod = function mod(num) {
  return this.divmod(num, 'mod', false).mod;
};

BN.prototype.umod = function umod(num) {
  return this.divmod(num, 'mod', true).mod;
};

// Find Round(`this` / `num`)
BN.prototype.divRound = function divRound(num) {
  var dm = this.divmod(num);

  // Fast case - exact division
  if (dm.mod.cmpn(0) === 0)
    return dm.div;

  var mod = dm.div.negative !== 0 ? dm.mod.isub(num) : dm.mod;

  var half = num.ushrn(1);
  var r2 = num.andln(1);
  var cmp = mod.cmp(half);

  // Round down
  if (cmp < 0 || r2 === 1 && cmp === 0)
    return dm.div;

  // Round up
  return dm.div.negative !== 0 ? dm.div.isubn(1) : dm.div.iaddn(1);
};

BN.prototype.modn = function modn(num) {
  var p = (1 << 26) % num;

  var acc = 0;
  for (var i = this.length - 1; i >= 0; i--)
    acc = (p * acc + (this.words[i] | 0)) % num;

  return acc;
};

// In-place division by number
BN.prototype.idivn = function idivn(num) {
  var carry = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var w = (this.words[i] | 0) + carry * 0x4000000;
    this.words[i] = (w / num) | 0;
    carry = w % num;
  }

  return this.strip();
};

BN.prototype.divn = function divn(num) {
  return this.clone().idivn(num);
};

BN.prototype.isEven = function isEven() {
  return (this.words[0] & 1) === 0;
};

BN.prototype.isOdd = function isOdd() {
  return (this.words[0] & 1) === 1;
};

// And first word and num
BN.prototype.andln = function andln(num) {
  return this.words[0] & num;
};

BN.prototype.cmpn = function cmpn(num) {
  var negative = num < 0;
  if (negative)
    num = -num;

  if (this.negative !== 0 && !negative)
    return -1;
  else if (this.negative === 0 && negative)
    return 1;

  num &= 0x3ffffff;
  this.strip();

  var res;
  if (this.length > 1) {
    res = 1;
  } else {
    var w = this.words[0] | 0;
    res = w === num ? 0 : w < num ? -1 : 1;
  }
  if (this.negative !== 0)
    res = -res;
  return res;
};

// Compare two numbers and return:
// 1 - if `this` > `num`
// 0 - if `this` == `num`
// -1 - if `this` < `num`
BN.prototype.cmp = function cmp(num) {
  if (this.negative !== 0 && num.negative === 0)
    return -1;
  else if (this.negative === 0 && num.negative !== 0)
    return 1;

  var res = this.ucmp(num);
  if (this.negative !== 0)
    return -res;
  else
    return res;
};

// Unsigned comparison
BN.prototype.ucmp = function ucmp(num) {
  // At this point both numbers have the same sign
  if (this.length > num.length)
    return 1;
  else if (this.length < num.length)
    return -1;

  var res = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var a = this.words[i] | 0;
    var b = num.words[i] | 0;

    if (a === b)
      continue;
    if (a < b)
      res = -1;
    else if (a > b)
      res = 1;
    break;
  }
  return res;
};
})(undefined, __bn);

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return {_:0, a:0, b:undefined};
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return {_:0, a:1, b:val};
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;
var __stable_table;

function makeStableName(x) {
    if(x instanceof Object) {
        if(!x.stableName) {
            x.stableName = __next_stable_name;
            __next_stable_name += 1;
        }
        return {type: 'obj', name: x.stableName};
    } else {
        return {type: 'prim', name: Number(x)};
    }
}

function eqStableName(x, y) {
    return (x.type == y.type && x.name == y.name) ? 1 : 0;
}

// TODO: inefficient compared to real fromInt?
__bn.Z = new __bn.BN(0);
__bn.ONE = new __bn.BN(1);
__bn.MOD32 = new __bn.BN(0x100000000); // 2^32
var I_fromNumber = function(x) {return new __bn.BN(x);}
var I_fromInt = I_fromNumber;
var I_fromBits = function(lo,hi) {
    var x = new __bn.BN(lo >>> 0);
    var y = new __bn.BN(hi >>> 0);
    y.ishln(32);
    x.iadd(y);
    return x;
}
var I_fromString = function(s) {return new __bn.BN(s);}
var I_toInt = function(x) {return I_toNumber(x.mod(__bn.MOD32));}
var I_toWord = function(x) {return I_toInt(x) >>> 0;};
// TODO: inefficient!
var I_toNumber = function(x) {return Number(x.toString());}
var I_equals = function(a,b) {return a.cmp(b) === 0;}
var I_compare = function(a,b) {return a.cmp(b);}
var I_compareInt = function(x,i) {return x.cmp(new __bn.BN(i));}
var I_negate = function(x) {return x.neg();}
var I_add = function(a,b) {return a.add(b);}
var I_sub = function(a,b) {return a.sub(b);}
var I_mul = function(a,b) {return a.mul(b);}
var I_mod = function(a,b) {return I_rem(I_add(b, I_rem(a, b)), b);}
var I_quotRem = function(a,b) {
    var qr = a.divmod(b);
    return {_:0, a:qr.div, b:qr.mod};
}
var I_div = function(a,b) {
    if((a.cmp(__bn.Z)>=0) != (a.cmp(__bn.Z)>=0)) {
        if(a.cmp(a.rem(b), __bn.Z) !== 0) {
            return a.div(b).sub(__bn.ONE);
        }
    }
    return a.div(b);
}
var I_divMod = function(a,b) {
    return {_:0, a:I_div(a,b), b:a.mod(b)};
}
var I_quot = function(a,b) {return a.div(b);}
var I_rem = function(a,b) {return a.mod(b);}
var I_and = function(a,b) {return a.and(b);}
var I_or = function(a,b) {return a.or(b);}
var I_xor = function(a,b) {return a.xor(b);}
var I_shiftLeft = function(a,b) {return a.shln(b);}
var I_shiftRight = function(a,b) {return a.shrn(b);}
var I_signum = function(x) {return x.cmp(new __bn.BN(0));}
var I_abs = function(x) {return x.abs();}
var I_decodeDouble = function(x) {
    var dec = decodeDouble(x);
    var mantissa = I_fromBits(dec.c, dec.b);
    if(dec.a < 0) {
        mantissa = I_negate(mantissa);
    }
    return {_:0, a:dec.d, b:mantissa};
}
var I_toString = function(x) {return x.toString();}
var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    if(x.isNegative()) {
        return I_negate(I_fromInt64(x.negate()));
    } else {
        return I_fromBits(x.low, x.high);
    }
}

function I_toInt64(x) {
    if(x.negative) {
        return I_toInt64(I_negate(x)).negate();
    } else {
        return new Long(I_toInt(x), I_toInt(I_shiftRight(x,32)));
    }
}

function I_fromWord64(x) {
    return I_fromBits(x.toInt(), x.shru(32).toInt());
}

function I_toWord64(x) {
    var w = I_toInt64(x);
    w.unsigned = true;
    return w;
}

/**
 * @license long.js (c) 2013 Daniel Wirtz <dcode@dcode.io>
 * Released under the Apache License, Version 2.0
 * see: https://github.com/dcodeIO/long.js for details
 */
function Long(low, high, unsigned) {
    this.low = low | 0;
    this.high = high | 0;
    this.unsigned = !!unsigned;
}

var INT_CACHE = {};
var UINT_CACHE = {};
function cacheable(x, u) {
    return u ? 0 <= (x >>>= 0) && x < 256 : -128 <= (x |= 0) && x < 128;
}

function __fromInt(value, unsigned) {
    var obj, cachedObj, cache;
    if (unsigned) {
        if (cache = cacheable(value >>>= 0, true)) {
            cachedObj = UINT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, (value | 0) < 0 ? -1 : 0, true);
        if (cache)
            UINT_CACHE[value] = obj;
        return obj;
    } else {
        if (cache = cacheable(value |= 0, false)) {
            cachedObj = INT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, value < 0 ? -1 : 0, false);
        if (cache)
            INT_CACHE[value] = obj;
        return obj;
    }
}

function __fromNumber(value, unsigned) {
    if (isNaN(value) || !isFinite(value))
        return unsigned ? UZERO : ZERO;
    if (unsigned) {
        if (value < 0)
            return UZERO;
        if (value >= TWO_PWR_64_DBL)
            return MAX_UNSIGNED_VALUE;
    } else {
        if (value <= -TWO_PWR_63_DBL)
            return MIN_VALUE;
        if (value + 1 >= TWO_PWR_63_DBL)
            return MAX_VALUE;
    }
    if (value < 0)
        return __fromNumber(-value, unsigned).neg();
    return new Long((value % TWO_PWR_32_DBL) | 0, (value / TWO_PWR_32_DBL) | 0, unsigned);
}
var pow_dbl = Math.pow;
var TWO_PWR_16_DBL = 1 << 16;
var TWO_PWR_24_DBL = 1 << 24;
var TWO_PWR_32_DBL = TWO_PWR_16_DBL * TWO_PWR_16_DBL;
var TWO_PWR_64_DBL = TWO_PWR_32_DBL * TWO_PWR_32_DBL;
var TWO_PWR_63_DBL = TWO_PWR_64_DBL / 2;
var TWO_PWR_24 = __fromInt(TWO_PWR_24_DBL);
var ZERO = __fromInt(0);
Long.ZERO = ZERO;
var UZERO = __fromInt(0, true);
Long.UZERO = UZERO;
var ONE = __fromInt(1);
Long.ONE = ONE;
var UONE = __fromInt(1, true);
Long.UONE = UONE;
var NEG_ONE = __fromInt(-1);
Long.NEG_ONE = NEG_ONE;
var MAX_VALUE = new Long(0xFFFFFFFF|0, 0x7FFFFFFF|0, false);
Long.MAX_VALUE = MAX_VALUE;
var MAX_UNSIGNED_VALUE = new Long(0xFFFFFFFF|0, 0xFFFFFFFF|0, true);
Long.MAX_UNSIGNED_VALUE = MAX_UNSIGNED_VALUE;
var MIN_VALUE = new Long(0, 0x80000000|0, false);
Long.MIN_VALUE = MIN_VALUE;
var __lp = Long.prototype;
__lp.toInt = function() {return this.unsigned ? this.low >>> 0 : this.low;};
__lp.toNumber = function() {
    if (this.unsigned)
        return ((this.high >>> 0) * TWO_PWR_32_DBL) + (this.low >>> 0);
    return this.high * TWO_PWR_32_DBL + (this.low >>> 0);
};
__lp.isZero = function() {return this.high === 0 && this.low === 0;};
__lp.isNegative = function() {return !this.unsigned && this.high < 0;};
__lp.isOdd = function() {return (this.low & 1) === 1;};
__lp.eq = function(other) {
    if (this.unsigned !== other.unsigned && (this.high >>> 31) === 1 && (other.high >>> 31) === 1)
        return false;
    return this.high === other.high && this.low === other.low;
};
__lp.neq = function(other) {return !this.eq(other);};
__lp.lt = function(other) {return this.comp(other) < 0;};
__lp.lte = function(other) {return this.comp(other) <= 0;};
__lp.gt = function(other) {return this.comp(other) > 0;};
__lp.gte = function(other) {return this.comp(other) >= 0;};
__lp.compare = function(other) {
    if (this.eq(other))
        return 0;
    var thisNeg = this.isNegative(),
        otherNeg = other.isNegative();
    if (thisNeg && !otherNeg)
        return -1;
    if (!thisNeg && otherNeg)
        return 1;
    if (!this.unsigned)
        return this.sub(other).isNegative() ? -1 : 1;
    return (other.high >>> 0) > (this.high >>> 0) || (other.high === this.high && (other.low >>> 0) > (this.low >>> 0)) ? -1 : 1;
};
__lp.comp = __lp.compare;
__lp.negate = function() {
    if (!this.unsigned && this.eq(MIN_VALUE))
        return MIN_VALUE;
    return this.not().add(ONE);
};
__lp.neg = __lp.negate;
__lp.add = function(addend) {
    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = addend.high >>> 16;
    var b32 = addend.high & 0xFFFF;
    var b16 = addend.low >>> 16;
    var b00 = addend.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 + b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 + b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 + b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 + b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.subtract = function(subtrahend) {return this.add(subtrahend.neg());};
__lp.sub = __lp.subtract;
__lp.multiply = function(multiplier) {
    if (this.isZero())
        return ZERO;
    if (multiplier.isZero())
        return ZERO;
    if (this.eq(MIN_VALUE))
        return multiplier.isOdd() ? MIN_VALUE : ZERO;
    if (multiplier.eq(MIN_VALUE))
        return this.isOdd() ? MIN_VALUE : ZERO;

    if (this.isNegative()) {
        if (multiplier.isNegative())
            return this.neg().mul(multiplier.neg());
        else
            return this.neg().mul(multiplier).neg();
    } else if (multiplier.isNegative())
        return this.mul(multiplier.neg()).neg();

    if (this.lt(TWO_PWR_24) && multiplier.lt(TWO_PWR_24))
        return __fromNumber(this.toNumber() * multiplier.toNumber(), this.unsigned);

    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = multiplier.high >>> 16;
    var b32 = multiplier.high & 0xFFFF;
    var b16 = multiplier.low >>> 16;
    var b00 = multiplier.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 * b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 * b00;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c16 += a00 * b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 * b00;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a16 * b16;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a00 * b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.mul = __lp.multiply;
__lp.divide = function(divisor) {
    if (divisor.isZero())
        throw Error('division by zero');
    if (this.isZero())
        return this.unsigned ? UZERO : ZERO;
    var approx, rem, res;
    if (this.eq(MIN_VALUE)) {
        if (divisor.eq(ONE) || divisor.eq(NEG_ONE))
            return MIN_VALUE;
        else if (divisor.eq(MIN_VALUE))
            return ONE;
        else {
            var halfThis = this.shr(1);
            approx = halfThis.div(divisor).shl(1);
            if (approx.eq(ZERO)) {
                return divisor.isNegative() ? ONE : NEG_ONE;
            } else {
                rem = this.sub(divisor.mul(approx));
                res = approx.add(rem.div(divisor));
                return res;
            }
        }
    } else if (divisor.eq(MIN_VALUE))
        return this.unsigned ? UZERO : ZERO;
    if (this.isNegative()) {
        if (divisor.isNegative())
            return this.neg().div(divisor.neg());
        return this.neg().div(divisor).neg();
    } else if (divisor.isNegative())
        return this.div(divisor.neg()).neg();

    res = ZERO;
    rem = this;
    while (rem.gte(divisor)) {
        approx = Math.max(1, Math.floor(rem.toNumber() / divisor.toNumber()));
        var log2 = Math.ceil(Math.log(approx) / Math.LN2),
            delta = (log2 <= 48) ? 1 : pow_dbl(2, log2 - 48),
            approxRes = __fromNumber(approx),
            approxRem = approxRes.mul(divisor);
        while (approxRem.isNegative() || approxRem.gt(rem)) {
            approx -= delta;
            approxRes = __fromNumber(approx, this.unsigned);
            approxRem = approxRes.mul(divisor);
        }
        if (approxRes.isZero())
            approxRes = ONE;

        res = res.add(approxRes);
        rem = rem.sub(approxRem);
    }
    return res;
};
__lp.div = __lp.divide;
__lp.modulo = function(divisor) {return this.sub(this.div(divisor).mul(divisor));};
__lp.mod = __lp.modulo;
__lp.not = function not() {return new Long(~this.low, ~this.high, this.unsigned);};
__lp.and = function(other) {return new Long(this.low & other.low, this.high & other.high, this.unsigned);};
__lp.or = function(other) {return new Long(this.low | other.low, this.high | other.high, this.unsigned);};
__lp.xor = function(other) {return new Long(this.low ^ other.low, this.high ^ other.high, this.unsigned);};

__lp.shl = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long(this.low << numBits, (this.high << numBits) | (this.low >>> (32 - numBits)), this.unsigned);
    else
        return new Long(0, this.low << (numBits - 32), this.unsigned);
};

__lp.shr = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long((this.low >>> numBits) | (this.high << (32 - numBits)), this.high >> numBits, this.unsigned);
    else
        return new Long(this.high >> (numBits - 32), this.high >= 0 ? 0 : -1, this.unsigned);
};

__lp.shru = function(numBits) {
    numBits &= 63;
    if (numBits === 0)
        return this;
    else {
        var high = this.high;
        if (numBits < 32) {
            var low = this.low;
            return new Long((low >>> numBits) | (high << (32 - numBits)), high >>> numBits, this.unsigned);
        } else if (numBits === 32)
            return new Long(high, 0, this.unsigned);
        else
            return new Long(high >>> (numBits - 32), 0, this.unsigned);
    }
};

__lp.toSigned = function() {return this.unsigned ? new Long(this.low, this.high, false) : this;};
__lp.toUnsigned = function() {return this.unsigned ? this : new Long(this.low, this.high, true);};

// Int64
function hs_eqInt64(x, y) {return x.eq(y);}
function hs_neInt64(x, y) {return x.neq(y);}
function hs_ltInt64(x, y) {return x.lt(y);}
function hs_leInt64(x, y) {return x.lte(y);}
function hs_gtInt64(x, y) {return x.gt(y);}
function hs_geInt64(x, y) {return x.gte(y);}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shl(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shr(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shru(bits);}
function hs_int64ToInt(x) {return x.toInt();}
var hs_intToInt64 = __fromInt;

// Word64
function hs_wordToWord64(x) {return __fromInt(x, true);}
function hs_word64ToWord(x) {return x.toInt(x);}
function hs_mkWord64(low, high) {return new Long(low,high,true);}
function hs_and64(a,b) {return a.and(b);};
function hs_or64(a,b) {return a.or(b);};
function hs_xor64(a,b) {return a.xor(b);};
function hs_not64(x) {return x.not();}
var hs_eqWord64 = hs_eqInt64;
var hs_neWord64 = hs_neInt64;
var hs_ltWord64 = hs_ltInt64;
var hs_leWord64 = hs_leInt64;
var hs_gtWord64 = hs_gtInt64;
var hs_geWord64 = hs_geInt64;
var hs_quotWord64 = hs_quotInt64;
var hs_remWord64 = hs_remInt64;
var hs_uncheckedShiftL64 = hs_uncheckedIShiftL64;
var hs_uncheckedShiftRL64 = hs_uncheckedIShiftRL64;
function hs_int64ToWord64(x) {return x.toUnsigned();}
function hs_word64ToInt64(x) {return x.toSigned();}

// Joseph Myers' MD5 implementation, ported to work on typed arrays.
// Used under the BSD license.
function md5cycle(x, k) {
    var a = x[0], b = x[1], c = x[2], d = x[3];

    a = ff(a, b, c, d, k[0], 7, -680876936);
    d = ff(d, a, b, c, k[1], 12, -389564586);
    c = ff(c, d, a, b, k[2], 17,  606105819);
    b = ff(b, c, d, a, k[3], 22, -1044525330);
    a = ff(a, b, c, d, k[4], 7, -176418897);
    d = ff(d, a, b, c, k[5], 12,  1200080426);
    c = ff(c, d, a, b, k[6], 17, -1473231341);
    b = ff(b, c, d, a, k[7], 22, -45705983);
    a = ff(a, b, c, d, k[8], 7,  1770035416);
    d = ff(d, a, b, c, k[9], 12, -1958414417);
    c = ff(c, d, a, b, k[10], 17, -42063);
    b = ff(b, c, d, a, k[11], 22, -1990404162);
    a = ff(a, b, c, d, k[12], 7,  1804603682);
    d = ff(d, a, b, c, k[13], 12, -40341101);
    c = ff(c, d, a, b, k[14], 17, -1502002290);
    b = ff(b, c, d, a, k[15], 22,  1236535329);

    a = gg(a, b, c, d, k[1], 5, -165796510);
    d = gg(d, a, b, c, k[6], 9, -1069501632);
    c = gg(c, d, a, b, k[11], 14,  643717713);
    b = gg(b, c, d, a, k[0], 20, -373897302);
    a = gg(a, b, c, d, k[5], 5, -701558691);
    d = gg(d, a, b, c, k[10], 9,  38016083);
    c = gg(c, d, a, b, k[15], 14, -660478335);
    b = gg(b, c, d, a, k[4], 20, -405537848);
    a = gg(a, b, c, d, k[9], 5,  568446438);
    d = gg(d, a, b, c, k[14], 9, -1019803690);
    c = gg(c, d, a, b, k[3], 14, -187363961);
    b = gg(b, c, d, a, k[8], 20,  1163531501);
    a = gg(a, b, c, d, k[13], 5, -1444681467);
    d = gg(d, a, b, c, k[2], 9, -51403784);
    c = gg(c, d, a, b, k[7], 14,  1735328473);
    b = gg(b, c, d, a, k[12], 20, -1926607734);

    a = hh(a, b, c, d, k[5], 4, -378558);
    d = hh(d, a, b, c, k[8], 11, -2022574463);
    c = hh(c, d, a, b, k[11], 16,  1839030562);
    b = hh(b, c, d, a, k[14], 23, -35309556);
    a = hh(a, b, c, d, k[1], 4, -1530992060);
    d = hh(d, a, b, c, k[4], 11,  1272893353);
    c = hh(c, d, a, b, k[7], 16, -155497632);
    b = hh(b, c, d, a, k[10], 23, -1094730640);
    a = hh(a, b, c, d, k[13], 4,  681279174);
    d = hh(d, a, b, c, k[0], 11, -358537222);
    c = hh(c, d, a, b, k[3], 16, -722521979);
    b = hh(b, c, d, a, k[6], 23,  76029189);
    a = hh(a, b, c, d, k[9], 4, -640364487);
    d = hh(d, a, b, c, k[12], 11, -421815835);
    c = hh(c, d, a, b, k[15], 16,  530742520);
    b = hh(b, c, d, a, k[2], 23, -995338651);

    a = ii(a, b, c, d, k[0], 6, -198630844);
    d = ii(d, a, b, c, k[7], 10,  1126891415);
    c = ii(c, d, a, b, k[14], 15, -1416354905);
    b = ii(b, c, d, a, k[5], 21, -57434055);
    a = ii(a, b, c, d, k[12], 6,  1700485571);
    d = ii(d, a, b, c, k[3], 10, -1894986606);
    c = ii(c, d, a, b, k[10], 15, -1051523);
    b = ii(b, c, d, a, k[1], 21, -2054922799);
    a = ii(a, b, c, d, k[8], 6,  1873313359);
    d = ii(d, a, b, c, k[15], 10, -30611744);
    c = ii(c, d, a, b, k[6], 15, -1560198380);
    b = ii(b, c, d, a, k[13], 21,  1309151649);
    a = ii(a, b, c, d, k[4], 6, -145523070);
    d = ii(d, a, b, c, k[11], 10, -1120210379);
    c = ii(c, d, a, b, k[2], 15,  718787259);
    b = ii(b, c, d, a, k[9], 21, -343485551);

    x[0] = add32(a, x[0]);
    x[1] = add32(b, x[1]);
    x[2] = add32(c, x[2]);
    x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
    a = add32(add32(a, q), add32(x, t));
    return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
    return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
    return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
    return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
    return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s, n) {
    var a = s['v']['w8'];
    var orig_n = n,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=n; i+=64) {
        md5cycle(state, md5blk(a.subarray(i-64, i)));
    }
    a = a.subarray(i-64);
    n = n < (i-64) ? 0 : n-(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<n; i++)
        tail[i>>2] |= a[i] << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = orig_n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s[i]
            + (s[i+1] << 8)
            + (s[i+2] << 16)
            + (s[i+3] << 24);
    }
    return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
    var s='', j=0;
    for(; j<4; j++)
        s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
        + hex_chr[(n >> (j * 8)) & 0x0F];
    return s;
}

function hex(x) {
    for (var i=0; i<x.length; i++)
        x[i] = rhex(x[i]);
    return x.join('');
}

function md5(s, n) {
    return hex(md51(s, n));
}

window['md5'] = md5;

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

function __hsbase_MD5Init(ctx) {}
// Note that this is a one time "update", since that's all that's used by
// GHC.Fingerprint.
function __hsbase_MD5Update(ctx, s, n) {
    ctx.md5 = md51(s, n);
}
function __hsbase_MD5Final(out, ctx) {
    var a = out['v']['i32'];
    a[0] = ctx.md5[0];
    a[1] = ctx.md5[1];
    a[2] = ctx.md5[2];
    a[3] = ctx.md5[3];
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = new Array(n);
    for(var i = 0; i < n; ++i) {
        arr[i] = x;
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    // Pad the thing to multiples of 8.
    var padding = 8 - n % 8;
    if(padding < 8) {
        n += padding;
    }
    return new ByteArray(new ArrayBuffer(n));
}

// Wrap a JS ArrayBuffer into a ByteArray. Truncates the array length to the
// closest multiple of 8 bytes.
function wrapByteArr(buffer) {
    var diff = buffer.byteLength % 8;
    if(diff != 0) {
        var buffer = buffer.slice(0, buffer.byteLength-diff);
    }
    return new ByteArray(buffer);
}

function ByteArray(buffer) {
    var views =
        { 'i8' : new Int8Array(buffer)
        , 'i16': new Int16Array(buffer)
        , 'i32': new Int32Array(buffer)
        , 'w8' : new Uint8Array(buffer)
        , 'w16': new Uint16Array(buffer)
        , 'w32': new Uint32Array(buffer)
        , 'f32': new Float32Array(buffer)
        , 'f64': new Float64Array(buffer)
        };
    this['b'] = buffer;
    this['v'] = views;
    this['off'] = 0;
}
window['newArr'] = newArr;
window['newByteArr'] = newByteArr;
window['wrapByteArr'] = wrapByteArr;
window['ByteArray'] = ByteArray;

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function writeOffAddr64(addr, off, x) {
    addr['v']['w32'][addr.off/8 + off*2] = x.low;
    addr['v']['w32'][addr.off/8 + off*2 + 1] = x.high;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

function readOffAddr64(signed, addr, off) {
    var w64 = hs_mkWord64( addr['v']['w32'][addr.off/8 + off*2]
                         , addr['v']['w32'][addr.off/8 + off*2 + 1]);
    return signed ? hs_word64ToInt64(w64) : w64;
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

// "Weak Pointers". Mostly useless implementation since
// JS does its own GC.

function mkWeak(key, val, fin) {
    fin = !fin? function() {}: fin;
    return {key: key, val: val, fin: fin};
}

function derefWeak(w) {
    return {_:0, a:1, b:E(w).val};
}

function finalizeWeak(w) {
    return {_:0, a:B(A1(E(w).fin, __Z))};
}

/* For foreign import ccall "wrapper" */
function createAdjustor(args, f, a, b) {
    return function(){
        var x = f.apply(null, arguments);
        while(x instanceof F) {x = x.f();}
        return x;
    };
}

var __apply = function(f,as) {
    var arr = [];
    for(; as._ === 1; as = as.b) {
        arr.push(as.a);
    }
    arr.reverse();
    return f.apply(null, arr);
}
var __app0 = function(f) {return f();}
var __app1 = function(f,a) {return f(a);}
var __app2 = function(f,a,b) {return f(a,b);}
var __app3 = function(f,a,b,c) {return f(a,b,c);}
var __app4 = function(f,a,b,c,d) {return f(a,b,c,d);}
var __app5 = function(f,a,b,c,d,e) {return f(a,b,c,d,e);}
var __jsNull = function() {return null;}
var __eq = function(a,b) {return a===b;}
var __createJSFunc = function(arity, f){
    if(f instanceof Function && arity === f.length) {
        return (function() {
            var x = f.apply(null,arguments);
            if(x instanceof T) {
                if(x.f !== __blackhole) {
                    var ff = x.f;
                    x.f = __blackhole;
                    return x.x = ff();
                }
                return x.x;
            } else {
                while(x instanceof F) {
                    x = x.f();
                }
                return E(x);
            }
        });
    } else {
        return (function(){
            var as = Array.prototype.slice.call(arguments);
            as.push(0);
            return E(B(A(f,as)));
        });
    }
}


function __arr2lst(elem,arr) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1,
            a:arr[elem],
            b:new T(function(){return __arr2lst(elem+1,arr);})};
}

function __lst2arr(xs) {
    var arr = [];
    xs = E(xs);
    for(;xs._ === 1; xs = E(xs.b)) {
        arr.push(E(xs.a));
    }
    return arr;
}

var __new = function() {return ({});}
var __set = function(o,k,v) {o[k]=v;}
var __get = function(o,k) {return o[k];}
var __has = function(o,k) {return o[k]!==undefined;}

var _0=0,_1=function(_){return _0;},_2=function(_3,_4){while(1){var _5=E(_3);if(!_5._){return E(_4);}else{_3=_5.b;_4=_5.a;continue;}}},_6=function(_7,_8,_9){return new F(function(){return _2(_8,_7);});},_a=function(_b,_c){var _d=E(_b);return (_d._==0)?E(_c):new T2(1,_d.a,new T(function(){return B(_a(_d.b,_c));}));},_e=new T(function(){return B(unCStr("!!: negative index"));}),_f=new T(function(){return B(unCStr("Prelude."));}),_g=new T(function(){return B(_a(_f,_e));}),_h=new T(function(){return B(err(_g));}),_i=new T(function(){return B(unCStr("!!: index too large"));}),_j=new T(function(){return B(_a(_f,_i));}),_k=new T(function(){return B(err(_j));}),_l=function(_m,_n){while(1){var _o=E(_m);if(!_o._){return E(_k);}else{var _p=E(_n);if(!_p){return E(_o.a);}else{_m=_o.b;_n=_p-1|0;continue;}}}},_q=function(_r,_s){if(_s>=0){return new F(function(){return _l(_r,_s);});}else{return E(_h);}},_t=function(_u){return E(E(_u).a);},_v=function(_w,_x,_y){while(1){var _z=E(_x);if(!_z._){return (E(_y)._==0)?true:false;}else{var _A=E(_y);if(!_A._){return false;}else{if(!B(A3(_t,_w,_z.a,_A.a))){return false;}else{_x=_z.b;_y=_A.b;continue;}}}}},_B=function(_C,_D,_E,_F,_G,_H){return (_C!=_F)?true:(E(_D)!=E(_G))?true:(E(_E)!=E(_H))?true:false;},_I=function(_J,_K){var _L=E(_J),_M=E(_L.a),_N=E(_K),_O=E(_N.a);return new F(function(){return _B(E(_M.a),_M.b,_L.b,E(_O.a),_O.b,_N.b);});},_P=function(_Q,_R){return E(_Q)==E(_R);},_S=function(_T,_U,_V,_W,_X,_Y){if(_T!=_W){return false;}else{if(E(_U)!=E(_X)){return false;}else{return new F(function(){return _P(_V,_Y);});}}},_Z=function(_10,_11){var _12=E(_10),_13=E(_12.a),_14=E(_11),_15=E(_14.a);return new F(function(){return _S(E(_13.a),_13.b,_12.b,E(_15.a),_15.b,_14.b);});},_16=new T2(0,_Z,_I),_17=function(_18,_19,_1a,_1b,_1c,_1d,_1e,_1f,_1g,_1h){while(1){var _1i=E(_1h);if(!_1i._){return {_:0,a:_18,b:_19,c:_1a,d:_1b,e:_1c,f:_1d,g:_1e,h:_1f,i:_1g};}else{var _1j=_1i.b,_1k=E(_1i.a),_1l=E(_1k.h);if(_1l<=_1f){_1h=_1j;continue;}else{_18=_1k.a;_19=_1k.b;_1a=_1k.c;_1b=_1k.d;_1c=_1k.e;_1d=_1k.f;_1e=_1k.g;_1f=_1l;_1g=_1k.i;_1h=_1j;continue;}}}},_1m=function(_1n,_1o,_1p,_1q,_1r,_1s,_1t,_1u,_1v,_1w){while(1){var _1x=E(_1w);if(!_1x._){return {_:0,a:_1n,b:_1o,c:_1p,d:_1q,e:_1r,f:_1s,g:_1t,h:_1u,i:_1v};}else{var _1y=_1x.b,_1z=E(_1x.a),_1A=E(_1z.h);if(_1A>=_1u){_1w=_1y;continue;}else{_1n=_1z.a;_1o=_1z.b;_1p=_1z.c;_1q=_1z.d;_1r=_1z.e;_1s=_1z.f;_1t=_1z.g;_1u=_1A;_1v=_1z.i;_1w=_1y;continue;}}}},_1B=function(_1C){var _1D=E(_1C);if(!_1D._){return true;}else{var _1E=_1D.b,_1F=E(E(_1D.a).a),_1G=_1F.b,_1H=E(_1F.a),_1I=function(_1J){if(E(_1H)==7){if(E(_1G)==1){return false;}else{return new F(function(){return _1B(_1E);});}}else{return new F(function(){return _1B(_1E);});}};if(E(_1H)==6){if(E(_1G)==1){return false;}else{return new F(function(){return _1I(_);});}}else{return new F(function(){return _1I(_);});}}},_1K=function(_1L,_1M){var _1N=E(E(_1L).a),_1O=_1N.b,_1P=E(_1N.a),_1Q=function(_1R){if(E(_1P)==7){if(E(_1O)==1){return false;}else{return new F(function(){return _1B(_1M);});}}else{return new F(function(){return _1B(_1M);});}};if(E(_1P)==6){if(E(_1O)==1){return false;}else{return new F(function(){return _1Q(_);});}}else{return new F(function(){return _1Q(_);});}},_1S=function(_1T){var _1U=E(_1T);if(!_1U._){return true;}else{var _1V=_1U.b,_1W=E(E(_1U.a).a),_1X=_1W.b,_1Y=E(_1W.a),_1Z=function(_20){var _21=function(_22){if(E(_1Y)==4){if(E(_1X)==1){return false;}else{return new F(function(){return _1S(_1V);});}}else{return new F(function(){return _1S(_1V);});}};if(E(_1Y)==3){if(E(_1X)==1){return false;}else{return new F(function(){return _21(_);});}}else{return new F(function(){return _21(_);});}};if(E(_1Y)==2){if(E(_1X)==1){return false;}else{return new F(function(){return _1Z(_);});}}else{return new F(function(){return _1Z(_);});}}},_23=function(_24,_25){var _26=E(E(_24).a),_27=_26.b,_28=E(_26.a),_29=function(_2a){var _2b=function(_2c){if(E(_28)==4){if(E(_27)==1){return false;}else{return new F(function(){return _1S(_25);});}}else{return new F(function(){return _1S(_25);});}};if(E(_28)==3){if(E(_27)==1){return false;}else{return new F(function(){return _2b(_);});}}else{return new F(function(){return _2b(_);});}};if(E(_28)==2){if(E(_27)==1){return false;}else{return new F(function(){return _29(_);});}}else{return new F(function(){return _29(_);});}},_2d=function(_2e){var _2f=E(_2e);if(!_2f._){return true;}else{var _2g=_2f.b,_2h=E(E(_2f.a).a),_2i=_2h.b,_2j=E(_2h.a),_2k=function(_2l){if(E(_2j)==7){if(E(_2i)==8){return false;}else{return new F(function(){return _2d(_2g);});}}else{return new F(function(){return _2d(_2g);});}};if(E(_2j)==6){if(E(_2i)==8){return false;}else{return new F(function(){return _2k(_);});}}else{return new F(function(){return _2k(_);});}}},_2m=function(_2n,_2o){var _2p=E(E(_2n).a),_2q=_2p.b,_2r=E(_2p.a),_2s=function(_2t){if(E(_2r)==7){if(E(_2q)==8){return false;}else{return new F(function(){return _2d(_2o);});}}else{return new F(function(){return _2d(_2o);});}};if(E(_2r)==6){if(E(_2q)==8){return false;}else{return new F(function(){return _2s(_);});}}else{return new F(function(){return _2s(_);});}},_2u=function(_2v){var _2w=E(_2v);if(!_2w._){return true;}else{var _2x=_2w.b,_2y=E(E(_2w.a).a),_2z=_2y.b,_2A=E(_2y.a),_2B=function(_2C){var _2D=function(_2E){if(E(_2A)==4){if(E(_2z)==8){return false;}else{return new F(function(){return _2u(_2x);});}}else{return new F(function(){return _2u(_2x);});}};if(E(_2A)==3){if(E(_2z)==8){return false;}else{return new F(function(){return _2D(_);});}}else{return new F(function(){return _2D(_);});}};if(E(_2A)==2){if(E(_2z)==1){return false;}else{return new F(function(){return _2B(_);});}}else{return new F(function(){return _2B(_);});}}},_2F=function(_2G,_2H){var _2I=E(E(_2G).a),_2J=_2I.b,_2K=E(_2I.a),_2L=function(_2M){var _2N=function(_2O){if(E(_2K)==4){if(E(_2J)==8){return false;}else{return new F(function(){return _2u(_2H);});}}else{return new F(function(){return _2u(_2H);});}};if(E(_2K)==3){if(E(_2J)==8){return false;}else{return new F(function(){return _2N(_);});}}else{return new F(function(){return _2N(_);});}};if(E(_2K)==2){if(E(_2J)==1){return false;}else{return new F(function(){return _2L(_);});}}else{return new F(function(){return _2L(_);});}},_2P=__Z,_2Q=new T(function(){return B(unCStr("base"));}),_2R=new T(function(){return B(unCStr("Control.Exception.Base"));}),_2S=new T(function(){return B(unCStr("PatternMatchFail"));}),_2T=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_2Q,_2R,_2S),_2U=new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_2T,_2P,_2P),_2V=function(_2W){return E(_2U);},_2X=function(_2Y){return E(E(_2Y).a);},_2Z=function(_30,_31,_32){var _33=B(A1(_30,_)),_34=B(A1(_31,_)),_35=hs_eqWord64(_33.a,_34.a);if(!_35){return __Z;}else{var _36=hs_eqWord64(_33.b,_34.b);return (!_36)?__Z:new T1(1,_32);}},_37=function(_38){var _39=E(_38);return new F(function(){return _2Z(B(_2X(_39.a)),_2V,_39.b);});},_3a=function(_3b){return E(E(_3b).a);},_3c=function(_3d){return new T2(0,_3e,_3d);},_3f=function(_3g,_3h){return new F(function(){return _a(E(_3g).a,_3h);});},_3i=44,_3j=93,_3k=91,_3l=function(_3m,_3n,_3o){var _3p=E(_3n);if(!_3p._){return new F(function(){return unAppCStr("[]",_3o);});}else{var _3q=new T(function(){var _3r=new T(function(){var _3s=function(_3t){var _3u=E(_3t);if(!_3u._){return E(new T2(1,_3j,_3o));}else{var _3v=new T(function(){return B(A2(_3m,_3u.a,new T(function(){return B(_3s(_3u.b));})));});return new T2(1,_3i,_3v);}};return B(_3s(_3p.b));});return B(A2(_3m,_3p.a,_3r));});return new T2(1,_3k,_3q);}},_3w=function(_3x,_3y){return new F(function(){return _3l(_3f,_3x,_3y);});},_3z=function(_3A,_3B,_3C){return new F(function(){return _a(E(_3B).a,_3C);});},_3D=new T3(0,_3z,_3a,_3w),_3e=new T(function(){return new T5(0,_2V,_3D,_3c,_37,_3a);}),_3E=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_3F=function(_3G){return E(E(_3G).c);},_3H=function(_3I,_3J){return new F(function(){return die(new T(function(){return B(A2(_3F,_3J,_3I));}));});},_3K=function(_3L,_3M){return new F(function(){return _3H(_3L,_3M);});},_3N=function(_3O,_3P){var _3Q=E(_3P);if(!_3Q._){return new T2(0,_2P,_2P);}else{var _3R=_3Q.a;if(!B(A1(_3O,_3R))){return new T2(0,_2P,_3Q);}else{var _3S=new T(function(){var _3T=B(_3N(_3O,_3Q.b));return new T2(0,_3T.a,_3T.b);});return new T2(0,new T2(1,_3R,new T(function(){return E(E(_3S).a);})),new T(function(){return E(E(_3S).b);}));}}},_3U=32,_3V=new T(function(){return B(unCStr("\n"));}),_3W=function(_3X){return (E(_3X)==124)?false:true;},_3Y=function(_3Z,_40){var _41=B(_3N(_3W,B(unCStr(_3Z)))),_42=_41.a,_43=function(_44,_45){var _46=new T(function(){var _47=new T(function(){return B(_a(_40,new T(function(){return B(_a(_45,_3V));},1)));});return B(unAppCStr(": ",_47));},1);return new F(function(){return _a(_44,_46);});},_48=E(_41.b);if(!_48._){return new F(function(){return _43(_42,_2P);});}else{if(E(_48.a)==124){return new F(function(){return _43(_42,new T2(1,_3U,_48.b));});}else{return new F(function(){return _43(_42,_2P);});}}},_49=function(_4a){return new F(function(){return _3K(new T1(0,new T(function(){return B(_3Y(_4a,_3E));})),_3e);});},_4b=new T(function(){return B(_49("Main.hs:(90,17)-(94,210)|function myrange"));}),_4c=function(_4d,_4e){while(1){var _4f=E(_4d);if(!_4f._){return E(_4e);}else{var _4g=new T2(1,_4f.a,_4e);_4d=_4f.b;_4e=_4g;continue;}}},_4h=new T(function(){return B(_4c(_2P,_2P));}),_4i=function(_4j,_4k,_4l,_4m){var _4n=new T(function(){return _4m>_4k;}),_4o=new T(function(){return _4k>_4m;});if(_4j!=_4l){if(_4k!=_4m){if(_4j>=_4l){if(_4l>=_4j){return E(_4b);}else{if(_4k>=_4m){if(_4l<=_4j){var _4p=function(_4q){var _4r=new T(function(){if(_4q!=_4j){return B(_4p(_4q+1|0));}else{return __Z;}});if(!E(_4n)){var _4s=function(_4t){while(1){var _4u=B((function(_4v){if((_4v-_4q|0)!=(_4k-_4j|0)){if(_4v!=_4k){var _4w=_4v+1|0;_4t=_4w;return __continue;}else{return E(_4r);}}else{return new T2(1,new T2(0,_4q,_4v),new T(function(){if(_4v!=_4k){return B(_4s(_4v+1|0));}else{return E(_4r);}}));}})(_4t));if(_4u!=__continue){return _4u;}}};return new F(function(){return _4s(_4m);});}else{return E(_4r);}};return new F(function(){return _4c(B(_4p(_4l)),_2P);});}else{return E(_4h);}}else{if(_4l<=_4j){var _4x=function(_4y){var _4z=new T(function(){if(_4y!=_4j){return B(_4x(_4y+1|0));}else{return __Z;}});if(!E(_4o)){var _4A=function(_4B){while(1){var _4C=B((function(_4D){if((_4y+_4D|0)!=(_4j+_4k|0)){if(_4D!=_4m){var _4E=_4D+1|0;_4B=_4E;return __continue;}else{return E(_4z);}}else{return new T2(1,new T2(0,_4y,_4D),new T(function(){if(_4D!=_4m){return B(_4A(_4D+1|0));}else{return E(_4z);}}));}})(_4B));if(_4C!=__continue){return _4C;}}};return new F(function(){return _4A(_4k);});}else{return E(_4z);}};return new F(function(){return _4x(_4l);});}else{return __Z;}}}}else{if(_4k>=_4m){if(_4j<=_4l){var _4F=function(_4G){var _4H=new T(function(){if(_4G!=_4l){return B(_4F(_4G+1|0));}else{return __Z;}});if(!E(_4n)){var _4I=function(_4J){while(1){var _4K=B((function(_4L){if((_4G+_4L|0)!=(_4j+_4k|0)){if(_4L!=_4k){var _4M=_4L+1|0;_4J=_4M;return __continue;}else{return E(_4H);}}else{return new T2(1,new T2(0,_4G,_4L),new T(function(){if(_4L!=_4k){return B(_4I(_4L+1|0));}else{return E(_4H);}}));}})(_4J));if(_4K!=__continue){return _4K;}}};return new F(function(){return _4I(_4m);});}else{return E(_4H);}};return new F(function(){return _4c(B(_4F(_4j)),_2P);});}else{return E(_4h);}}else{if(_4j<=_4l){var _4N=function(_4O){var _4P=new T(function(){if(_4O!=_4l){return B(_4N(_4O+1|0));}else{return __Z;}});if(!E(_4o)){var _4Q=function(_4R){while(1){var _4S=B((function(_4T){if((_4T-_4O|0)!=(_4k-_4j|0)){if(_4T!=_4m){var _4U=_4T+1|0;_4R=_4U;return __continue;}else{return E(_4P);}}else{return new T2(1,new T2(0,_4O,_4T),new T(function(){if(_4T!=_4m){return B(_4Q(_4T+1|0));}else{return E(_4P);}}));}})(_4R));if(_4S!=__continue){return _4S;}}};return new F(function(){return _4Q(_4k);});}else{return E(_4P);}};return new F(function(){return _4N(_4j);});}else{return __Z;}}}}else{if(_4j>=_4l){if(_4l<=_4j){var _4V=function(_4W){var _4X=new T(function(){if(_4W!=_4j){return B(_4V(_4W+1|0));}else{return __Z;}});if(!E(_4n)){var _4Y=function(_4Z){return new T2(1,new T2(0,_4W,_4Z),new T(function(){if(_4Z!=_4k){return B(_4Y(_4Z+1|0));}else{return E(_4X);}}));};return new F(function(){return _4Y(_4m);});}else{return E(_4X);}};return new F(function(){return _4c(B(_4V(_4l)),_2P);});}else{return E(_4h);}}else{if(_4j<=_4l){var _50=function(_51){var _52=new T(function(){if(_51!=_4l){return B(_50(_51+1|0));}else{return __Z;}}),_53=function(_54){return new T2(1,new T2(0,_51,_54),new T(function(){if(_54!=_4m){return B(_53(_54+1|0));}else{return E(_52);}}));};return new F(function(){return _53(_4m);});};return new F(function(){return _50(_4j);});}else{return __Z;}}}}else{if(_4k>=_4m){if(_4l<=_4j){var _55=function(_56){var _57=new T(function(){if(_56!=_4j){return B(_55(_56+1|0));}else{return __Z;}});if(!E(_4n)){var _58=function(_59){return new T2(1,new T2(0,_56,_59),new T(function(){if(_59!=_4k){return B(_58(_59+1|0));}else{return E(_57);}}));};return new F(function(){return _58(_4m);});}else{return E(_57);}};return new F(function(){return _4c(B(_55(_4l)),_2P);});}else{return E(_4h);}}else{if(_4j<=_4l){var _5a=function(_5b){var _5c=new T(function(){if(_5b!=_4l){return B(_5a(_5b+1|0));}else{return __Z;}});if(!E(_4o)){var _5d=function(_5e){return new T2(1,new T2(0,_5b,_5e),new T(function(){if(_5e!=_4m){return B(_5d(_5e+1|0));}else{return E(_5c);}}));};return new F(function(){return _5d(_4k);});}else{return E(_5c);}};return new F(function(){return _5a(_4j);});}else{return __Z;}}}},_5f=function(_5g,_5h,_5i,_5j,_5k,_5l,_5m,_5n,_5o,_5p,_5q){var _5r=E(_5q);if(!_5r._){return {_:0,a:_5h,b:_5i,c:_5j,d:_5k,e:_5l,f:_5m,g:_5n,h:_5o,i:_5p};}else{var _5s=_5r.a,_5t=_5r.b;if(!E(_5g)){var _5u=E(_5s),_5v=E(_5u.h),_5w=E(_5o);if(_5v>=_5w){return new F(function(){return _1m(_5h,_5i,_5j,_5k,_5l,_5m,_5n,_5w,_5p,_5t);});}else{return new F(function(){return _1m(_5u.a,_5u.b,_5u.c,_5u.d,_5u.e,_5u.f,_5u.g,_5v,_5u.i,_5t);});}}else{var _5x=E(_5s),_5y=E(_5x.h),_5z=E(_5o);if(_5y<=_5z){return new F(function(){return _17(_5h,_5i,_5j,_5k,_5l,_5m,_5n,_5z,_5p,_5t);});}else{return new F(function(){return _17(_5x.a,_5x.b,_5x.c,_5x.d,_5x.e,_5x.f,_5x.g,_5y,_5x.i,_5t);});}}}},_5A=new T(function(){return B(_49("Main.hs:(198,1)-(200,70)|function replace"));}),_5B=function(_5C,_5D,_5E){var _5F=E(_5C);switch(_5F){case -1:var _5G=E(_5E);return (_5G._==0)?E(_5A):E(_5G);case 0:var _5H=E(_5E);return (_5H._==0)?E(_5A):new T2(1,_5D,_5H.b);default:var _5I=E(_5E);return (_5I._==0)?E(_5A):new T2(1,_5I.a,new T(function(){return B(_5B(_5F-1|0,_5D,_5I.b));}));}},_5J=false,_5K=__Z,_5L=true,_5M=new T(function(){return B(unCStr(": empty list"));}),_5N=function(_5O){return new F(function(){return err(B(_a(_f,new T(function(){return B(_a(_5O,_5M));},1))));});},_5P=new T(function(){return B(unCStr("head"));}),_5Q=new T(function(){return B(_5N(_5P));}),_5R=function(_5S,_5T){while(1){var _5U=B((function(_5V,_5W){var _5X=E(_5W);if(!_5X._){return __Z;}else{var _5Y=_5X.a,_5Z=_5X.b;if(!B(A1(_5V,_5Y))){var _60=_5V;_5S=_60;_5T=_5Z;return __continue;}else{return new T2(1,_5Y,new T(function(){return B(_5R(_5V,_5Z));}));}}})(_5S,_5T));if(_5U!=__continue){return _5U;}}},_61=function(_62){while(1){var _63=B((function(_64){var _65=E(_64);if(!_65._){return true;}else{var _66=_65.b,_67=E(_65.a),_68=u_iswlower(E(_67.b));if(!E(_68)){var _69=E(_67.a),_6a=_69.b,_6b=E(_69.a),_6c=function(_6d){var _6e=function(_6f){if(E(_6b)==5){if(E(_6a)==8){return false;}else{return new F(function(){return _61(_66);});}}else{return new F(function(){return _61(_66);});}};if(E(_6b)==4){if(E(_6a)==8){return false;}else{return new F(function(){return _6e(_);});}}else{return new F(function(){return _6e(_);});}};if(E(_6b)==3){if(E(_6a)==8){return false;}else{return new F(function(){return _6c(_);});}}else{return new F(function(){return _6c(_);});}}else{_62=_66;return __continue;}}})(_62));if(_63!=__continue){return _63;}}},_6g=function(_6h){while(1){var _6i=E(_6h);if(!_6i._){return true;}else{if(!B(_61(_6i.a))){return false;}else{_6h=_6i.b;continue;}}}},_6j=function(_6k){while(1){var _6l=B((function(_6m){var _6n=E(_6m);if(!_6n._){return true;}else{var _6o=_6n.b,_6p=E(_6n.a),_6q=u_iswlower(E(_6p.b));if(!E(_6q)){var _6r=E(_6p.a),_6s=_6r.b,_6t=E(_6r.a),_6u=function(_6v){var _6w=function(_6x){if(E(_6t)==7){if(E(_6s)==8){return false;}else{return new F(function(){return _6j(_6o);});}}else{return new F(function(){return _6j(_6o);});}};if(E(_6t)==6){if(E(_6s)==8){return false;}else{return new F(function(){return _6w(_);});}}else{return new F(function(){return _6w(_);});}};if(E(_6t)==5){if(E(_6s)==8){return false;}else{return new F(function(){return _6u(_);});}}else{return new F(function(){return _6u(_);});}}else{_6k=_6o;return __continue;}}})(_6k));if(_6l!=__continue){return _6l;}}},_6y=function(_6z){while(1){var _6A=E(_6z);if(!_6A._){return true;}else{if(!B(_6j(_6A.a))){return false;}else{_6z=_6A.b;continue;}}}},_6B=function(_6C){while(1){var _6D=B((function(_6E){var _6F=E(_6E);if(!_6F._){return true;}else{var _6G=_6F.b,_6H=E(_6F.a),_6I=u_iswupper(E(_6H.b));if(!E(_6I)){var _6J=E(_6H.a),_6K=_6J.b,_6L=E(_6J.a),_6M=function(_6N){var _6O=function(_6P){if(E(_6L)==5){if(E(_6K)==1){return false;}else{return new F(function(){return _6B(_6G);});}}else{return new F(function(){return _6B(_6G);});}};if(E(_6L)==4){if(E(_6K)==1){return false;}else{return new F(function(){return _6O(_);});}}else{return new F(function(){return _6O(_);});}};if(E(_6L)==3){if(E(_6K)==1){return false;}else{return new F(function(){return _6M(_);});}}else{return new F(function(){return _6M(_);});}}else{_6C=_6G;return __continue;}}})(_6C));if(_6D!=__continue){return _6D;}}},_6Q=function(_6R){while(1){var _6S=E(_6R);if(!_6S._){return true;}else{if(!B(_6B(_6S.a))){return false;}else{_6R=_6S.b;continue;}}}},_6T=function(_6U){while(1){var _6V=B((function(_6W){var _6X=E(_6W);if(!_6X._){return true;}else{var _6Y=_6X.b,_6Z=E(_6X.a),_70=u_iswupper(E(_6Z.b));if(!E(_70)){var _71=E(_6Z.a),_72=_71.b,_73=E(_71.a),_74=function(_75){var _76=function(_77){if(E(_73)==7){if(E(_72)==1){return false;}else{return new F(function(){return _6T(_6Y);});}}else{return new F(function(){return _6T(_6Y);});}};if(E(_73)==6){if(E(_72)==1){return false;}else{return new F(function(){return _76(_);});}}else{return new F(function(){return _76(_);});}};if(E(_73)==5){if(E(_72)==1){return false;}else{return new F(function(){return _74(_);});}}else{return new F(function(){return _74(_);});}}else{_6U=_6Y;return __continue;}}})(_6U));if(_6V!=__continue){return _6V;}}},_78=function(_79){while(1){var _7a=E(_79);if(!_7a._){return true;}else{if(!B(_6T(_7a.a))){return false;}else{_79=_7a.b;continue;}}}},_7b=function(_7c){while(1){var _7d=E(_7c);if(!_7d._){return true;}else{if(!E(_7d.a)){return false;}else{_7c=_7d.b;continue;}}}},_7e=function(_7f,_7g){while(1){var _7h=E(_7f);if(!_7h._){return E(_7g);}else{var _7i=_7h.b;switch(E(E(_7h.a).b)){case 66:var _7j=_7g+3.75;_7f=_7i;_7g=_7j;continue;case 78:var _7j=_7g+3.5;_7f=_7i;_7g=_7j;continue;case 80:var _7j=_7g+1;_7f=_7i;_7g=_7j;continue;case 81:var _7j=_7g+9;_7f=_7i;_7g=_7j;continue;case 82:var _7j=_7g+5;_7f=_7i;_7g=_7j;continue;case 98:var _7j=_7g+(-3.75);_7f=_7i;_7g=_7j;continue;case 110:var _7j=_7g+(-3.5);_7f=_7i;_7g=_7j;continue;case 112:var _7j=_7g+(-1);_7f=_7i;_7g=_7j;continue;case 113:var _7j=_7g+(-9);_7f=_7i;_7g=_7j;continue;case 114:var _7j=_7g+(-5);_7f=_7i;_7g=_7j;continue;default:_7f=_7i;continue;}}}},_7k=function(_7l,_7m){while(1){var _7n=E(_7l);if(!_7n._){return E(_7m);}else{var _7o=_7n.b,_7p=E(_7n.a);if(E(_7p.b)==82){switch(E(E(_7p.a).a)){case 4:var _7q=_7m+0.5;_7l=_7o;_7m=_7q;continue;case 5:var _7q=_7m+0.5;_7l=_7o;_7m=_7q;continue;default:_7l=_7o;continue;}}else{_7l=_7o;continue;}}}},_7r=function(_7s,_7t){while(1){var _7u=E(_7s);if(!_7u._){return E(_7t);}else{var _7v=_7u.b,_7w=E(_7u.a);if(E(_7w.b)==114){switch(E(E(_7w.a).a)){case 4:var _7x=_7t+(-0.5);_7s=_7v;_7t=_7x;continue;case 5:var _7x=_7t+(-0.5);_7s=_7v;_7t=_7x;continue;default:_7s=_7v;continue;}}else{_7s=_7v;continue;}}}},_7y=function(_7z,_7A){while(1){var _7B=E(_7z);if(!_7B._){return E(_7A);}else{var _7C=_7B.b,_7D=E(_7B.a);if(E(_7D.b)==80){var _7E=E(_7D.a),_7F=E(_7E.b);if(_7F<6){switch(E(_7E.a)){case 4:if(_7F<4){_7z=_7C;continue;}else{var _7G=_7A+0.6;_7z=_7C;_7A=_7G;continue;}break;case 5:if(_7F<4){_7z=_7C;continue;}else{var _7G=_7A+0.6;_7z=_7C;_7A=_7G;continue;}break;default:_7z=_7C;continue;}}else{var _7G=_7A+0.6;_7z=_7C;_7A=_7G;continue;}}else{_7z=_7C;continue;}}}},_7H=function(_7I,_7J){while(1){var _7K=E(_7I);if(!_7K._){return E(_7J);}else{var _7L=_7K.b,_7M=E(_7K.a);if(E(_7M.b)==112){var _7N=E(_7M.a),_7O=E(_7N.b);if(_7O>3){switch(E(_7N.a)){case 4:if(_7O>5){_7I=_7L;continue;}else{var _7P=_7J+(-0.6);_7I=_7L;_7J=_7P;continue;}break;case 5:if(_7O>5){_7I=_7L;continue;}else{var _7P=_7J+(-0.6);_7I=_7L;_7J=_7P;continue;}break;default:_7I=_7L;continue;}}else{var _7P=_7J+(-0.6);_7I=_7L;_7J=_7P;continue;}}else{_7I=_7L;continue;}}}},_7Q=function(_7R,_7S){while(1){var _7T=B((function(_7U,_7V){var _7W=E(_7U);if(!_7W._){return E(_7V);}else{var _7X=_7W.b,_7Y=E(_7W.a),_7Z=function(_80){if(E(E(_7Y.a).b)==1){return new F(function(){return _7Q(_7X,_80+(-0.3));});}else{return new F(function(){return _7Q(_7X,_80);});}};switch(E(_7Y.b)){case 66:return new F(function(){return _7Z(_7V);});break;case 78:return new F(function(){return _7Z(_7V);});break;default:var _81=_7V;_7R=_7X;_7S=_81;return __continue;}}})(_7R,_7S));if(_7T!=__continue){return _7T;}}},_82=function(_83,_84){while(1){var _85=B((function(_86,_87){var _88=E(_86);if(!_88._){return E(_87);}else{var _89=_88.b,_8a=E(_88.a),_8b=function(_8c){if(E(E(_8a.a).b)==8){return new F(function(){return _82(_89,_8c+0.3);});}else{return new F(function(){return _82(_89,_8c);});}};switch(E(_8a.b)){case 98:return new F(function(){return _8b(_87);});break;case 110:return new F(function(){return _8b(_87);});break;default:var _8d=_87;_83=_89;_84=_8d;return __continue;}}})(_83,_84));if(_85!=__continue){return _85;}}},_8e=function(_8f,_8g,_8h,_8i,_8j,_8k,_8l,_8m){var _8n=new T(function(){var _8o=B(_7e(_8f,0)),_8p=B(_7k(_8f,0)),_8q=B(_7r(_8f,0)),_8r=B(_7y(_8f,0)),_8s=B(_7H(_8f,0)),_8t=B(_7Q(_8f,0)),_8u=B(_82(_8f,0)),_8v=function(_8w){return (!B(_q(_8i,2)))?(!B(_q(_8i,3)))?(!B(_q(_8h,2)))?(!B(_q(_8h,3)))?_8o+_8p+_8q+_8r+_8s+_8t+_8u+_8w:_8o+_8p+_8q+_8r+_8s+_8t+_8u+_8w+0.5:(!B(_q(_8h,3)))?_8o+_8p+_8q+_8r+_8s+_8t+_8u+_8w+0.5:_8o+_8p+_8q+_8r+_8s+_8t+_8u+_8w+1:_8o+_8p+_8q+_8r+_8s+_8t+_8u+_8w+(-0.9):_8o+_8p+_8q+_8r+_8s+_8t+_8u+_8w+(-0.9);};if(!B(_q(_8i,0))){if(!B(_q(_8i,1))){var _8x=function(_8y){if(!B(_q(_8h,1))){return new F(function(){return _8v(_8y);});}else{return new F(function(){return _8v(_8y+(-0.5));});}};if(!B(_q(_8h,0))){return B(_8x(0));}else{return B(_8x(-0.5));}}else{return B(_8v(0.9));}}else{return B(_8v(0.9));}});return {_:0,a:_8f,b:_8g,c:_8h,d:_8i,e:_8j,f:_8k,g:_8n,h:_8l,i:_8m};},_8z=function(_8A){var _8B=E(_8A),_8C=B(_8e(_8B.a,_8B.b,_8B.c,_8B.d,_8B.e,_8B.f,_8B.h,_8B.i));return {_:0,a:_8C.a,b:_8C.b,c:_8C.c,d:_8C.d,e:_8C.e,f:_8C.f,g:_8C.g,h:_8C.h,i:_8C.i};},_8D=function(_8E,_8F){var _8G=E(_8F);return (_8G._==0)?__Z:new T2(1,_8E,new T(function(){return B(_8D(_8G.a,_8G.b));}));},_8H=new T(function(){return B(unCStr("init"));}),_8I=new T(function(){return B(_5N(_8H));}),_8J=function(_8K){return E(E(_8K).a);},_8L=0,_8M=2,_8N=3,_8O=4,_8P=5,_8Q=6,_8R=0,_8S=new T2(0,_8R,_8R),_8T=82,_8U=1,_8V=new T2(0,_8Q,_8U),_8W=new T2(0,_8V,_8T),_8X=75,_8Y=7,_8Z=new T2(0,_8Y,_8U),_90=new T2(0,_8Z,_8X),_91=new T2(0,_8O,_8U),_92=new T2(0,_91,_8T),_93=new T2(0,_8N,_8U),_94=new T2(0,_93,_8X),_95=114,_96=8,_97=new T2(0,_8Q,_96),_98=new T2(0,_97,_95),_99=107,_9a=new T2(0,_8Y,_96),_9b=new T2(0,_9a,_99),_9c=new T2(0,_8O,_96),_9d=new T2(0,_9c,_8T),_9e=new T2(0,_8N,_96),_9f=new T2(0,_9e,_99),_9g=function(_9h){var _9i=new T(function(){var _9j=E(_9h);if(!_9j){return __Z;}else{return B(_9g(_9j+1|0));}}),_9k=new T(function(){return B(_9l(1));}),_9l=function(_9m){if(!E(_9h)){var _9n=E(_9m);if(!_9n){return E(_9k);}else{var _9o=new T(function(){var _9p=E(_9n);if(_9p==8){return E(_9i);}else{var _9q=function(_9r){var _9s=E(_9r);return (_9s==0)?E(_9k):new T2(1,new T2(0,_9h,_9s),new T(function(){var _9t=E(_9s);if(_9t==8){return E(_9i);}else{return B(_9q(_9t+1|0));}}));};return B(_9q(_9p+1|0));}});return new T2(1,new T2(0,_9h,_9n),_9o);}}else{var _9u=new T(function(){var _9v=E(_9m);if(_9v==8){return E(_9i);}else{var _9w=function(_9x){return new T2(1,new T2(0,_9h,_9x),new T(function(){var _9y=E(_9x);if(_9y==8){return E(_9i);}else{return B(_9w(_9y+1|0));}}));};return B(_9w(_9v+1|0));}});return new T2(1,new T2(0,_9h,_9m),_9u);}};return new F(function(){return _9l(-8);});},_9z=new T(function(){return B(_9g(0));}),_9A=function(_9B){while(1){var _9C=B((function(_9D){var _9E=E(_9D);if(!_9E){_9B=1;return __continue;}else{return new T2(1,new T2(0,_9E,0),new T(function(){var _9F=E(_9E);if(_9F==8){return E(_9z);}else{return B(_9A(_9F+1|0));}}));}})(_9B));if(_9C!=__continue){return _9C;}}},_9G=new T(function(){return B(_9A(-8));}),_9H=function(_9I){while(1){var _9J=B((function(_9K){var _9L=E(_9K);if(!_9L){_9I=1;return __continue;}else{return new T2(0,new T2(0,_9L, -_9L),new T(function(){var _9M=E(_9L);if(_9M==8){return E(_9G);}else{var _9N=B(_9H(_9M+1|0));return new T2(1,_9N.a,_9N.b);}}));}})(_9I));if(_9J!=__continue){return _9J;}}},_9O=new T(function(){var _9P=B(_9H(-8));return new T2(1,_9P.a,_9P.b);}),_9Q=function(_9R){while(1){var _9S=B((function(_9T){var _9U=E(_9T);if(!_9U){_9R=1;return __continue;}else{return new T2(0,new T2(0,_9U,_9U),new T(function(){var _9V=E(_9U);if(_9V==8){return E(_9O);}else{var _9W=B(_9Q(_9V+1|0));return new T2(1,_9W.a,_9W.b);}}));}})(_9R));if(_9S!=__continue){return _9S;}}},_9X=new T(function(){var _9Y=B(_9Q(-8));return new T2(1,_9Y.a,_9Y.b);}),_9Z=81,_a0=78,_a1=function(_a2){while(1){var _a3=B((function(_a4){var _a5=E(_a4);if(!_a5){_a2=1;return __continue;}else{return new T2(0,new T2(0,_a5, -_a5),new T(function(){var _a6=E(_a5);if(_a6==8){return __Z;}else{var _a7=B(_a1(_a6+1|0));return new T2(1,_a7.a,_a7.b);}}));}})(_a2));if(_a3!=__continue){return _a3;}}},_a8=new T(function(){var _a9=B(_a1(-8));return new T2(1,_a9.a,_a9.b);}),_aa=function(_ab){while(1){var _ac=B((function(_ad){var _ae=E(_ad);if(!_ae){_ab=1;return __continue;}else{return new T2(0,new T2(0,_ae,_ae),new T(function(){var _af=E(_ae);if(_af==8){return E(_a8);}else{var _ag=B(_aa(_af+1|0));return new T2(1,_ag.a,_ag.b);}}));}})(_ab));if(_ac!=__continue){return _ac;}}},_ah=new T(function(){var _ai=B(_aa(-8));return new T2(1,_ai.a,_ai.b);}),_aj=66,_ak=function(_al){var _am=new T(function(){var _an=E(_al);if(!_an){return __Z;}else{return B(_ak(_an+1|0));}}),_ao=new T(function(){return B(_ap(1));}),_ap=function(_aq){if(!E(_al)){var _ar=E(_aq);if(!_ar){return E(_ao);}else{var _as=new T(function(){var _at=E(_ar);if(_at==8){return E(_am);}else{var _au=function(_av){var _aw=E(_av);return (_aw==0)?E(_ao):new T2(1,new T2(0,_al,_aw),new T(function(){var _ax=E(_aw);if(_ax==8){return E(_am);}else{return B(_au(_ax+1|0));}}));};return B(_au(_at+1|0));}});return new T2(1,new T2(0,_al,_ar),_as);}}else{var _ay=new T(function(){var _az=E(_aq);if(_az==8){return E(_am);}else{var _aA=function(_aB){return new T2(1,new T2(0,_al,_aB),new T(function(){var _aC=E(_aB);if(_aC==8){return E(_am);}else{return B(_aA(_aC+1|0));}}));};return B(_aA(_az+1|0));}});return new T2(1,new T2(0,_al,_aq),_ay);}};return new F(function(){return _ap(-8);});},_aD=new T(function(){return B(_ak(0));}),_aE=function(_aF){while(1){var _aG=B((function(_aH){var _aI=E(_aH);if(!_aI){_aF=1;return __continue;}else{return new T2(1,new T2(0,_aI,0),new T(function(){var _aJ=E(_aI);if(_aJ==8){return E(_aD);}else{return B(_aE(_aJ+1|0));}}));}})(_aF));if(_aG!=__continue){return _aG;}}},_aK=new T(function(){return B(_aE(-8));}),_aL=80,_aM=function(_aN){var _aO=new T(function(){var _aP=E(_aN);if(!_aP){return __Z;}else{return B(_aM(_aP+1|0));}}),_aQ=new T(function(){return B(_aR(1));}),_aR=function(_aS){if(!E(_aN)){var _aT=E(_aS);if(!_aT){return E(_aQ);}else{var _aU=new T(function(){var _aV=E(_aT);if(_aV==8){return E(_aO);}else{var _aW=function(_aX){var _aY=E(_aX);return (_aY==0)?E(_aQ):new T2(1,new T2(0,_aN,_aY),new T(function(){var _aZ=E(_aY);if(_aZ==8){return E(_aO);}else{return B(_aW(_aZ+1|0));}}));};return B(_aW(_aV+1|0));}});return new T2(1,new T2(0,_aN,_aT),_aU);}}else{var _b0=new T(function(){var _b1=E(_aS);if(_b1==8){return E(_aO);}else{var _b2=function(_b3){return new T2(1,new T2(0,_aN,_b3),new T(function(){var _b4=E(_b3);if(_b4==8){return E(_aO);}else{return B(_b2(_b4+1|0));}}));};return B(_b2(_b1+1|0));}});return new T2(1,new T2(0,_aN,_aS),_b0);}};return new F(function(){return _aR(-8);});},_b5=new T(function(){return B(_aM(0));}),_b6=function(_b7){while(1){var _b8=B((function(_b9){var _ba=E(_b9);if(!_ba){_b7=1;return __continue;}else{return new T2(1,new T2(0,_ba,0),new T(function(){var _bb=E(_ba);if(_bb==8){return E(_b5);}else{return B(_b6(_bb+1|0));}}));}})(_b7));if(_b8!=__continue){return _b8;}}},_bc=new T(function(){return B(_b6(-8));}),_bd=function(_be){while(1){var _bf=B((function(_bg){var _bh=E(_bg);if(!_bh){_be=1;return __continue;}else{return new T2(0,new T2(0,_bh, -_bh),new T(function(){var _bi=E(_bh);if(_bi==8){return E(_bc);}else{var _bj=B(_bd(_bi+1|0));return new T2(1,_bj.a,_bj.b);}}));}})(_be));if(_bf!=__continue){return _bf;}}},_bk=new T(function(){var _bl=B(_bd(-8));return new T2(1,_bl.a,_bl.b);}),_bm=function(_bn){while(1){var _bo=B((function(_bp){var _bq=E(_bp);if(!_bq){_bn=1;return __continue;}else{return new T2(0,new T2(0,_bq,_bq),new T(function(){var _br=E(_bq);if(_br==8){return E(_bk);}else{var _bs=B(_bm(_br+1|0));return new T2(1,_bs.a,_bs.b);}}));}})(_bn));if(_bo!=__continue){return _bo;}}},_bt=new T(function(){var _bu=B(_bm(-8));return new T2(1,_bu.a,_bu.b);}),_bv=113,_bw=110,_bx=function(_by){while(1){var _bz=B((function(_bA){var _bB=E(_bA);if(!_bB){_by=1;return __continue;}else{return new T2(0,new T2(0,_bB, -_bB),new T(function(){var _bC=E(_bB);if(_bC==8){return __Z;}else{var _bD=B(_bx(_bC+1|0));return new T2(1,_bD.a,_bD.b);}}));}})(_by));if(_bz!=__continue){return _bz;}}},_bE=new T(function(){var _bF=B(_bx(-8));return new T2(1,_bF.a,_bF.b);}),_bG=function(_bH){while(1){var _bI=B((function(_bJ){var _bK=E(_bJ);if(!_bK){_bH=1;return __continue;}else{return new T2(0,new T2(0,_bK,_bK),new T(function(){var _bL=E(_bK);if(_bL==8){return E(_bE);}else{var _bM=B(_bG(_bL+1|0));return new T2(1,_bM.a,_bM.b);}}));}})(_bH));if(_bI!=__continue){return _bI;}}},_bN=new T(function(){var _bO=B(_bG(-8));return new T2(1,_bO.a,_bO.b);}),_bP=98,_bQ=function(_bR){var _bS=new T(function(){var _bT=E(_bR);if(!_bT){return __Z;}else{return B(_bQ(_bT+1|0));}}),_bU=new T(function(){return B(_bV(1));}),_bV=function(_bW){if(!E(_bR)){var _bX=E(_bW);if(!_bX){return E(_bU);}else{var _bY=new T(function(){var _bZ=E(_bX);if(_bZ==8){return E(_bS);}else{var _c0=function(_c1){var _c2=E(_c1);return (_c2==0)?E(_bU):new T2(1,new T2(0,_bR,_c2),new T(function(){var _c3=E(_c2);if(_c3==8){return E(_bS);}else{return B(_c0(_c3+1|0));}}));};return B(_c0(_bZ+1|0));}});return new T2(1,new T2(0,_bR,_bX),_bY);}}else{var _c4=new T(function(){var _c5=E(_bW);if(_c5==8){return E(_bS);}else{var _c6=function(_c7){return new T2(1,new T2(0,_bR,_c7),new T(function(){var _c8=E(_c7);if(_c8==8){return E(_bS);}else{return B(_c6(_c8+1|0));}}));};return B(_c6(_c5+1|0));}});return new T2(1,new T2(0,_bR,_bW),_c4);}};return new F(function(){return _bV(-8);});},_c9=new T(function(){return B(_bQ(0));}),_ca=function(_cb){while(1){var _cc=B((function(_cd){var _ce=E(_cd);if(!_ce){_cb=1;return __continue;}else{return new T2(1,new T2(0,_ce,0),new T(function(){var _cf=E(_ce);if(_cf==8){return E(_c9);}else{return B(_ca(_cf+1|0));}}));}})(_cb));if(_cc!=__continue){return _cc;}}},_cg=new T(function(){return B(_ca(-8));}),_ch=112,_ci=-2.1472688996352e9,_cj=2.1472688986353e9,_ck=function(_cl,_cm){var _cn=E(_cm);return (_cn._==0)?__Z:new T2(1,new T(function(){return B(A1(_cl,_cn.a));}),new T(function(){return B(_ck(_cl,_cn.b));}));},_co=function(_cp){return (!E(_cp))?true:false;},_cq=new T(function(){return B(unCStr("tail"));}),_cr=new T(function(){return B(_5N(_cq));}),_cs=new T2(1,_2P,_2P),_ct=function(_cu,_cv){var _cw=function(_cx,_cy){var _cz=E(_cx);if(!_cz._){return E(_cy);}else{var _cA=_cz.a,_cB=E(_cy);if(!_cB._){return E(_cz);}else{var _cC=_cB.a;return (B(A2(_cu,_cA,_cC))==2)?new T2(1,_cC,new T(function(){return B(_cw(_cz,_cB.b));})):new T2(1,_cA,new T(function(){return B(_cw(_cz.b,_cB));}));}}},_cD=function(_cE){var _cF=E(_cE);if(!_cF._){return __Z;}else{var _cG=E(_cF.b);return (_cG._==0)?E(_cF):new T2(1,new T(function(){return B(_cw(_cF.a,_cG.a));}),new T(function(){return B(_cD(_cG.b));}));}},_cH=new T(function(){return B(_cI(B(_cD(_2P))));}),_cI=function(_cJ){while(1){var _cK=E(_cJ);if(!_cK._){return E(_cH);}else{if(!E(_cK.b)._){return E(_cK.a);}else{_cJ=B(_cD(_cK));continue;}}}},_cL=new T(function(){return B(_cM(_2P));}),_cN=function(_cO,_cP,_cQ){while(1){var _cR=B((function(_cS,_cT,_cU){var _cV=E(_cU);if(!_cV._){return new T2(1,new T2(1,_cS,_cT),_cL);}else{var _cW=_cV.a;if(B(A2(_cu,_cS,_cW))==2){var _cX=new T2(1,_cS,_cT);_cO=_cW;_cP=_cX;_cQ=_cV.b;return __continue;}else{return new T2(1,new T2(1,_cS,_cT),new T(function(){return B(_cM(_cV));}));}}})(_cO,_cP,_cQ));if(_cR!=__continue){return _cR;}}},_cY=function(_cZ,_d0,_d1){while(1){var _d2=B((function(_d3,_d4,_d5){var _d6=E(_d5);if(!_d6._){return new T2(1,new T(function(){return B(A1(_d4,new T2(1,_d3,_2P)));}),_cL);}else{var _d7=_d6.a,_d8=_d6.b;switch(B(A2(_cu,_d3,_d7))){case 0:_cZ=_d7;_d0=function(_d9){return new F(function(){return A1(_d4,new T2(1,_d3,_d9));});};_d1=_d8;return __continue;case 1:_cZ=_d7;_d0=function(_da){return new F(function(){return A1(_d4,new T2(1,_d3,_da));});};_d1=_d8;return __continue;default:return new T2(1,new T(function(){return B(A1(_d4,new T2(1,_d3,_2P)));}),new T(function(){return B(_cM(_d6));}));}}})(_cZ,_d0,_d1));if(_d2!=__continue){return _d2;}}},_cM=function(_db){var _dc=E(_db);if(!_dc._){return E(_cs);}else{var _dd=_dc.a,_de=E(_dc.b);if(!_de._){return new T2(1,_dc,_2P);}else{var _df=_de.a,_dg=_de.b;if(B(A2(_cu,_dd,_df))==2){return new F(function(){return _cN(_df,new T2(1,_dd,_2P),_dg);});}else{return new F(function(){return _cY(_df,function(_dh){return new T2(1,_dd,_dh);},_dg);});}}}};return new F(function(){return _cI(B(_cM(_cv)));});},_di=2147483647,_dj=-2147483648,_dk=function(_dl,_dm,_dn,_do,_dp,_dq,_dr,_ds,_dt,_du,_dv,_dw){var _dx=new T(function(){return B(_q(_dr,3));}),_dy=new T(function(){return B(_q(_dr,2));}),_dz=new T(function(){return B(_q(_dr,1));}),_dA=new T(function(){return B(_q(_dr,0));});if(_dl>0){var _dB=E(_dp);if(!_dB._){return {_:0,a:_2P,b:_dq,c:_dr,d:_ds,e:_dt,f:_du,g:_dv,h:new T(function(){if(!E(_dq)){return E(_dj);}else{return E(_di);}}),i:_5K};}else{var _dC=_dB.a,_dD=_dB.b,_dE=new T(function(){var _dF=E(_dC),_dG=_dF.a,_dH=E(_dF.b);if(!E(_dq)){if(E(_dH)==107){return new T2(0,_dG,_dH);}else{var _dI=function(_dJ){while(1){var _dK=E(_dJ);if(!_dK._){return E(_5Q);}else{var _dL=E(_dK.a),_dM=E(_dL.b);if(E(_dM)==107){return new T2(0,_dL.a,_dM);}else{_dJ=_dK.b;continue;}}}},_dN=B(_dI(_dD));return new T2(0,_dN.a,_dN.b);}}else{if(E(_dH)==75){return new T2(0,_dG,_dH);}else{var _dO=function(_dP){while(1){var _dQ=E(_dP);if(!_dQ._){return E(_5Q);}else{var _dR=E(_dQ.a),_dS=E(_dR.b);if(E(_dS)==75){return new T2(0,_dR.a,_dS);}else{_dP=_dQ.b;continue;}}}},_dT=B(_dO(_dD));return new T2(0,_dT.a,_dT.b);}}}),_dU=new T(function(){return B(_5B(0,_5L,B(_5B(1,_5L,_dr))));}),_dV=new T(function(){if(!B(_7b(_dr))){var _dW=function(_dX){var _dY=function(_dZ){var _e0=function(_e1){if(!E(_dq)){if(!E(_dx)){if(!B(_2F(_dC,_dD))){return __Z;}else{var _e2=new T(function(){var _e3=function(_e4){var _e5=E(_e4),_e6=E(_e5.a),_e7=_e6.b,_e8=E(_e6.a),_e9=function(_ea){var _eb=E(_dE),_ec=E(_eb.a);return (_e8!=E(_ec.a))?true:(E(_e7)!=E(_ec.b))?true:(E(_e5.b)!=E(_eb.b))?true:false;};if(E(_e8)==1){if(E(_e7)==8){return false;}else{return new F(function(){return _e9(_);});}}else{return new F(function(){return _e9(_);});}};return B(_5R(_e3,_dB));});return new T2(1,{_:0,a:new T2(1,_9f,new T2(1,_9d,_e2)),b:_5L,c:new T(function(){return B(_5B(2,_5L,B(_5B(3,_5L,_dr))));}),d:new T(function(){return B(_5B(3,_5L,_ds));}),e:_8U,f:_8S,g:_8L,h:_8L,i:_5K},_2P);}}else{return __Z;}}else{return __Z;}};if(!E(_dq)){if(!E(_dy)){if(!B(_2m(_dC,_dD))){return new F(function(){return _e0(_);});}else{var _ed=new T(function(){var _ee=function(_ef){var _eg=E(_ef),_eh=E(_eg.a),_ei=_eh.b,_ej=E(_eh.a),_ek=function(_el){var _em=E(_dE),_en=E(_em.a);return (_ej!=E(_en.a))?true:(E(_ei)!=E(_en.b))?true:(E(_eg.b)!=E(_em.b))?true:false;};if(E(_ej)==8){if(E(_ei)==8){return false;}else{return new F(function(){return _ek(_);});}}else{return new F(function(){return _ek(_);});}};return B(_5R(_ee,_dB));});return new T2(1,{_:0,a:new T2(1,_9b,new T2(1,_98,_ed)),b:_5L,c:new T(function(){return B(_5B(2,_5L,B(_5B(3,_5L,_dr))));}),d:new T(function(){return B(_5B(2,_5L,_ds));}),e:_8U,f:_8S,g:_8L,h:_8L,i:_5K},_2P);}}else{return new F(function(){return _e0(_);});}}else{return new F(function(){return _e0(_);});}};if(!E(_dq)){return new F(function(){return _dY(_);});}else{if(!E(_dz)){if(!B(_23(_dC,_dD))){return new F(function(){return _dY(_);});}else{var _eo=new T(function(){var _ep=function(_eq){var _er=E(_eq),_es=E(_er.a),_et=_es.b,_eu=E(_es.a),_ev=function(_ew){var _ex=E(_dE),_ey=E(_ex.a);return (_eu!=E(_ey.a))?true:(E(_et)!=E(_ey.b))?true:(E(_er.b)!=E(_ex.b))?true:false;};if(E(_eu)==1){if(E(_et)==1){return false;}else{return new F(function(){return _ev(_);});}}else{return new F(function(){return _ev(_);});}};return B(_5R(_ep,_dB));});return new T2(1,{_:0,a:new T2(1,_94,new T2(1,_92,_eo)),b:_5J,c:_dU,d:new T(function(){return B(_5B(1,_5L,_ds));}),e:_8U,f:_8S,g:_8L,h:_8L,i:_5K},_2P);}}else{return new F(function(){return _dY(_);});}}};if(!E(_dq)){return B(_dW(_));}else{if(!E(_dA)){if(!B(_1K(_dC,_dD))){return B(_dW(_));}else{var _ez=new T(function(){var _eA=function(_eB){var _eC=E(_eB),_eD=E(_eC.a),_eE=_eD.b,_eF=E(_eD.a),_eG=function(_eH){var _eI=E(_dE),_eJ=E(_eI.a);return (_eF!=E(_eJ.a))?true:(E(_eE)!=E(_eJ.b))?true:(E(_eC.b)!=E(_eI.b))?true:false;};if(E(_eF)==8){if(E(_eE)==1){return false;}else{return new F(function(){return _eG(_);});}}else{return new F(function(){return _eG(_);});}};return B(_5R(_eA,_dB));});return new T2(1,{_:0,a:new T2(1,_90,new T2(1,_8W,_ez)),b:_5J,c:_dU,d:new T(function(){return B(_5B(0,_5L,_ds));}),e:_8U,f:_8S,g:_8L,h:_8L,i:_5K},_2P);}}else{return B(_dW(_));}}}else{return __Z;}});if(!E(_dq)){var _eK=new T(function(){var _eL=new T(function(){var _eM=new T(function(){var _eN=new T(function(){var _eO=new T(function(){var _eP=new T(function(){var _eQ=new T(function(){var _eR=new T(function(){var _eS=new T(function(){return B(_5B(3,_5L,B(_5B(2,_5L,_dr))));}),_eT=function(_eU,_eV,_eW){var _eX=E(_dE),_eY=E(_eX.a),_eZ=E(_eY.a),_f0=_eZ+_eU|0;if(_f0<1){return E(_eW);}else{if(_f0>8){return E(_eW);}else{var _f1=E(_eY.b),_f2=_f1+_eV|0;if(_f2<1){return E(_eW);}else{if(_f2>8){return E(_eW);}else{var _f3=function(_f4){while(1){var _f5=E(_f4);if(!_f5._){return true;}else{var _f6=_f5.b,_f7=E(_f5.a),_f8=E(_f7.a);if(E(_f8.a)!=_f0){_f4=_f6;continue;}else{if(E(_f8.b)!=_f2){_f4=_f6;continue;}else{var _f9=u_iswupper(E(_f7.b));if(!E(_f9)){return false;}else{_f4=_f6;continue;}}}}}};if(!B((function(_fa,_fb){var _fc=E(_fa),_fd=E(_fc.a);if(E(_fd.a)!=_f0){return new F(function(){return _f3(_fb);});}else{if(E(_fd.b)!=_f2){return new F(function(){return _f3(_fb);});}else{var _fe=u_iswupper(E(_fc.b));if(!E(_fe)){return false;}else{return new F(function(){return _f3(_fb);});}}}})(_dC,_dD))){return E(_eW);}else{var _ff=new T(function(){var _fg=function(_fh){while(1){var _fi=E(_fh);if(!_fi._){return false;}else{var _fj=_fi.b,_fk=E(E(_fi.a).a);if(E(_fk.a)!=_f0){_fh=_fj;continue;}else{if(E(_fk.b)!=_f2){_fh=_fj;continue;}else{return true;}}}}};if(!B((function(_fl,_fm){var _fn=E(E(_fl).a);if(E(_fn.a)!=_f0){return new F(function(){return _fg(_fm);});}else{if(E(_fn.b)!=_f2){return new F(function(){return _fg(_fm);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_fo=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_f0)==8){if(E(_f2)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_f0)==1){if(E(_f2)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_eS))));}),_fp=new T(function(){var _fq=function(_fr){var _fs=E(_fr),_ft=E(_fs.a),_fu=_ft.b,_fv=E(_ft.a),_fw=function(_fx){return (_fv!=_eZ)?true:(E(_fu)!=_f1)?true:(E(_fs.b)!=E(_eX.b))?true:false;};if(_fv!=_f0){return new F(function(){return _fw(_);});}else{if(E(_fu)!=_f2){return new F(function(){return _fw(_);});}else{return false;}}};return B(_5R(_fq,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_f0,_f2),_99),_fp),b:_5L,c:_fo,d:_ds,e:_ff,f:_8S,g:_8L,h:_8L,i:_5K},_eW);}}}}}},_fy=new T(function(){var _fz=new T(function(){var _fA=new T(function(){var _fB=new T(function(){var _fC=new T(function(){var _fD=new T(function(){return B(_eT(-1,-1,new T(function(){return B(_eT(-1,0,_dV));})));});return B(_eT(0,-1,_fD));});return B(_eT(1,-1,_fC));});return B(_eT(1,0,_fB));});return B(_eT(1,1,_fA));});return B(_eT(0,1,_fz));});return B(_eT(-1,1,_fy));}),_fE=function(_fF){while(1){var _fG=B((function(_fH){var _fI=E(_fH);if(!_fI._){return true;}else{var _fJ=_fI.b,_fK=E(E(_dC).a),_fL=E(_fI.a),_fM=_fL.b,_fN=E(_fL.a);if(E(_fK.a)!=_fN){var _fO=function(_fP){while(1){var _fQ=E(_fP);if(!_fQ._){return true;}else{var _fR=_fQ.b,_fS=E(E(_fQ.a).a);if(E(_fS.a)!=_fN){_fP=_fR;continue;}else{if(E(_fS.b)!=E(_fM)){_fP=_fR;continue;}else{return false;}}}}};if(!B(_fO(_dD))){return false;}else{_fF=_fJ;return __continue;}}else{var _fT=E(_fM);if(E(_fK.b)!=_fT){var _fU=function(_fV){while(1){var _fW=E(_fV);if(!_fW._){return true;}else{var _fX=_fW.b,_fY=E(E(_fW.a).a);if(E(_fY.a)!=_fN){_fV=_fX;continue;}else{if(E(_fY.b)!=_fT){_fV=_fX;continue;}else{return false;}}}}};if(!B(_fU(_dD))){return false;}else{_fF=_fJ;return __continue;}}else{return false;}}}})(_fF));if(_fG!=__continue){return _fG;}}},_fZ=function(_g0){var _g1=E(_g0);if(!_g1._){return E(_eR);}else{var _g2=E(_g1.a),_g3=new T(function(){return B(_fZ(_g1.b));});if(E(_g2.b)==113){var _g4=E(_bt);if(!_g4._){return E(_g3);}else{var _g5=_g4.b,_g6=E(_g2.a),_g7=_g6.b,_g8=E(_g6.a),_g9=E(_g4.a),_ga=_g8+E(_g9.a)|0;if(_ga<1){var _gb=function(_gc){while(1){var _gd=B((function(_ge){var _gf=E(_ge);if(!_gf._){return E(_g3);}else{var _gg=_gf.b,_gh=E(_gf.a),_gi=_g8+E(_gh.a)|0;if(_gi<1){_gc=_gg;return __continue;}else{if(_gi>8){_gc=_gg;return __continue;}else{var _gj=E(_g7),_gk=_gj+E(_gh.b)|0;if(_gk<1){_gc=_gg;return __continue;}else{if(_gk>8){_gc=_gg;return __continue;}else{var _gl=B(_4i(_g8,_gj,_gi,_gk));if(!_gl._){return E(_cr);}else{var _gm=E(_gl.b);if(!_gm._){return E(_8I);}else{if(!B(_fE(B(_8D(_gm.a,_gm.b))))){_gc=_gg;return __continue;}else{var _gn=function(_go){while(1){var _gp=E(_go);if(!_gp._){return true;}else{var _gq=_gp.b,_gr=E(_gp.a),_gs=E(_gr.a);if(E(_gs.a)!=_gi){_go=_gq;continue;}else{if(E(_gs.b)!=_gk){_go=_gq;continue;}else{var _gt=u_iswupper(E(_gr.b));if(!E(_gt)){return false;}else{_go=_gq;continue;}}}}}};if(!B((function(_gu,_gv){var _gw=E(_gu),_gx=E(_gw.a);if(E(_gx.a)!=_gi){return new F(function(){return _gn(_gv);});}else{if(E(_gx.b)!=_gk){return new F(function(){return _gn(_gv);});}else{var _gy=u_iswupper(E(_gw.b));if(!E(_gy)){return false;}else{return new F(function(){return _gn(_gv);});}}}})(_dC,_dD))){_gc=_gg;return __continue;}else{var _gz=new T(function(){var _gA=function(_gB){while(1){var _gC=E(_gB);if(!_gC._){return false;}else{var _gD=_gC.b,_gE=E(E(_gC.a).a);if(E(_gE.a)!=_gi){_gB=_gD;continue;}else{if(E(_gE.b)!=_gk){_gB=_gD;continue;}else{return true;}}}}};if(!B((function(_gF,_gG){var _gH=E(E(_gF).a);if(E(_gH.a)!=_gi){return new F(function(){return _gA(_gG);});}else{if(E(_gH.b)!=_gk){return new F(function(){return _gA(_gG);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_gI=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_gi)==8){if(E(_gk)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_gi)==1){if(E(_gk)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_gJ=new T(function(){var _gK=function(_gL){var _gM=E(_gL),_gN=E(_gM.a),_gO=_gN.b,_gP=E(_gN.a),_gQ=function(_gR){return (_gP!=_g8)?true:(E(_gO)!=_gj)?true:(E(_gM.b)==113)?false:true;};if(_gP!=_gi){return new F(function(){return _gQ(_);});}else{if(E(_gO)!=_gk){return new F(function(){return _gQ(_);});}else{return false;}}};return B(_5R(_gK,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_gi,_gk),_bv),_gJ),b:_5L,c:_gI,d:_ds,e:_gz,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_gb(_gg));}));}}}}}}}}}})(_gc));if(_gd!=__continue){return _gd;}}};return new F(function(){return _gb(_g5);});}else{if(_ga>8){var _gS=function(_gT){while(1){var _gU=B((function(_gV){var _gW=E(_gV);if(!_gW._){return E(_g3);}else{var _gX=_gW.b,_gY=E(_gW.a),_gZ=_g8+E(_gY.a)|0;if(_gZ<1){_gT=_gX;return __continue;}else{if(_gZ>8){_gT=_gX;return __continue;}else{var _h0=E(_g7),_h1=_h0+E(_gY.b)|0;if(_h1<1){_gT=_gX;return __continue;}else{if(_h1>8){_gT=_gX;return __continue;}else{var _h2=B(_4i(_g8,_h0,_gZ,_h1));if(!_h2._){return E(_cr);}else{var _h3=E(_h2.b);if(!_h3._){return E(_8I);}else{if(!B(_fE(B(_8D(_h3.a,_h3.b))))){_gT=_gX;return __continue;}else{var _h4=function(_h5){while(1){var _h6=E(_h5);if(!_h6._){return true;}else{var _h7=_h6.b,_h8=E(_h6.a),_h9=E(_h8.a);if(E(_h9.a)!=_gZ){_h5=_h7;continue;}else{if(E(_h9.b)!=_h1){_h5=_h7;continue;}else{var _ha=u_iswupper(E(_h8.b));if(!E(_ha)){return false;}else{_h5=_h7;continue;}}}}}};if(!B((function(_hb,_hc){var _hd=E(_hb),_he=E(_hd.a);if(E(_he.a)!=_gZ){return new F(function(){return _h4(_hc);});}else{if(E(_he.b)!=_h1){return new F(function(){return _h4(_hc);});}else{var _hf=u_iswupper(E(_hd.b));if(!E(_hf)){return false;}else{return new F(function(){return _h4(_hc);});}}}})(_dC,_dD))){_gT=_gX;return __continue;}else{var _hg=new T(function(){var _hh=function(_hi){while(1){var _hj=E(_hi);if(!_hj._){return false;}else{var _hk=_hj.b,_hl=E(E(_hj.a).a);if(E(_hl.a)!=_gZ){_hi=_hk;continue;}else{if(E(_hl.b)!=_h1){_hi=_hk;continue;}else{return true;}}}}};if(!B((function(_hm,_hn){var _ho=E(E(_hm).a);if(E(_ho.a)!=_gZ){return new F(function(){return _hh(_hn);});}else{if(E(_ho.b)!=_h1){return new F(function(){return _hh(_hn);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_hp=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_gZ)==8){if(E(_h1)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_gZ)==1){if(E(_h1)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_hq=new T(function(){var _hr=function(_hs){var _ht=E(_hs),_hu=E(_ht.a),_hv=_hu.b,_hw=E(_hu.a),_hx=function(_hy){return (_hw!=_g8)?true:(E(_hv)!=_h0)?true:(E(_ht.b)==113)?false:true;};if(_hw!=_gZ){return new F(function(){return _hx(_);});}else{if(E(_hv)!=_h1){return new F(function(){return _hx(_);});}else{return false;}}};return B(_5R(_hr,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_gZ,_h1),_bv),_hq),b:_5L,c:_hp,d:_ds,e:_hg,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_gS(_gX));}));}}}}}}}}}})(_gT));if(_gU!=__continue){return _gU;}}};return new F(function(){return _gS(_g5);});}else{var _hz=E(_g7),_hA=_hz+E(_g9.b)|0;if(_hA<1){var _hB=function(_hC){while(1){var _hD=B((function(_hE){var _hF=E(_hE);if(!_hF._){return E(_g3);}else{var _hG=_hF.b,_hH=E(_hF.a),_hI=_g8+E(_hH.a)|0;if(_hI<1){_hC=_hG;return __continue;}else{if(_hI>8){_hC=_hG;return __continue;}else{var _hJ=_hz+E(_hH.b)|0;if(_hJ<1){_hC=_hG;return __continue;}else{if(_hJ>8){_hC=_hG;return __continue;}else{var _hK=B(_4i(_g8,_hz,_hI,_hJ));if(!_hK._){return E(_cr);}else{var _hL=E(_hK.b);if(!_hL._){return E(_8I);}else{if(!B(_fE(B(_8D(_hL.a,_hL.b))))){_hC=_hG;return __continue;}else{var _hM=function(_hN){while(1){var _hO=E(_hN);if(!_hO._){return true;}else{var _hP=_hO.b,_hQ=E(_hO.a),_hR=E(_hQ.a);if(E(_hR.a)!=_hI){_hN=_hP;continue;}else{if(E(_hR.b)!=_hJ){_hN=_hP;continue;}else{var _hS=u_iswupper(E(_hQ.b));if(!E(_hS)){return false;}else{_hN=_hP;continue;}}}}}};if(!B((function(_hT,_hU){var _hV=E(_hT),_hW=E(_hV.a);if(E(_hW.a)!=_hI){return new F(function(){return _hM(_hU);});}else{if(E(_hW.b)!=_hJ){return new F(function(){return _hM(_hU);});}else{var _hX=u_iswupper(E(_hV.b));if(!E(_hX)){return false;}else{return new F(function(){return _hM(_hU);});}}}})(_dC,_dD))){_hC=_hG;return __continue;}else{var _hY=new T(function(){var _hZ=function(_i0){while(1){var _i1=E(_i0);if(!_i1._){return false;}else{var _i2=_i1.b,_i3=E(E(_i1.a).a);if(E(_i3.a)!=_hI){_i0=_i2;continue;}else{if(E(_i3.b)!=_hJ){_i0=_i2;continue;}else{return true;}}}}};if(!B((function(_i4,_i5){var _i6=E(E(_i4).a);if(E(_i6.a)!=_hI){return new F(function(){return _hZ(_i5);});}else{if(E(_i6.b)!=_hJ){return new F(function(){return _hZ(_i5);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_i7=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_hI)==8){if(E(_hJ)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_hI)==1){if(E(_hJ)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_i8=new T(function(){var _i9=function(_ia){var _ib=E(_ia),_ic=E(_ib.a),_id=_ic.b,_ie=E(_ic.a),_if=function(_ig){return (_ie!=_g8)?true:(E(_id)!=_hz)?true:(E(_ib.b)==113)?false:true;};if(_ie!=_hI){return new F(function(){return _if(_);});}else{if(E(_id)!=_hJ){return new F(function(){return _if(_);});}else{return false;}}};return B(_5R(_i9,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_hI,_hJ),_bv),_i8),b:_5L,c:_i7,d:_ds,e:_hY,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_hB(_hG));}));}}}}}}}}}})(_hC));if(_hD!=__continue){return _hD;}}};return new F(function(){return _hB(_g5);});}else{if(_hA>8){var _ih=function(_ii){while(1){var _ij=B((function(_ik){var _il=E(_ik);if(!_il._){return E(_g3);}else{var _im=_il.b,_in=E(_il.a),_io=_g8+E(_in.a)|0;if(_io<1){_ii=_im;return __continue;}else{if(_io>8){_ii=_im;return __continue;}else{var _ip=_hz+E(_in.b)|0;if(_ip<1){_ii=_im;return __continue;}else{if(_ip>8){_ii=_im;return __continue;}else{var _iq=B(_4i(_g8,_hz,_io,_ip));if(!_iq._){return E(_cr);}else{var _ir=E(_iq.b);if(!_ir._){return E(_8I);}else{if(!B(_fE(B(_8D(_ir.a,_ir.b))))){_ii=_im;return __continue;}else{var _is=function(_it){while(1){var _iu=E(_it);if(!_iu._){return true;}else{var _iv=_iu.b,_iw=E(_iu.a),_ix=E(_iw.a);if(E(_ix.a)!=_io){_it=_iv;continue;}else{if(E(_ix.b)!=_ip){_it=_iv;continue;}else{var _iy=u_iswupper(E(_iw.b));if(!E(_iy)){return false;}else{_it=_iv;continue;}}}}}};if(!B((function(_iz,_iA){var _iB=E(_iz),_iC=E(_iB.a);if(E(_iC.a)!=_io){return new F(function(){return _is(_iA);});}else{if(E(_iC.b)!=_ip){return new F(function(){return _is(_iA);});}else{var _iD=u_iswupper(E(_iB.b));if(!E(_iD)){return false;}else{return new F(function(){return _is(_iA);});}}}})(_dC,_dD))){_ii=_im;return __continue;}else{var _iE=new T(function(){var _iF=function(_iG){while(1){var _iH=E(_iG);if(!_iH._){return false;}else{var _iI=_iH.b,_iJ=E(E(_iH.a).a);if(E(_iJ.a)!=_io){_iG=_iI;continue;}else{if(E(_iJ.b)!=_ip){_iG=_iI;continue;}else{return true;}}}}};if(!B((function(_iK,_iL){var _iM=E(E(_iK).a);if(E(_iM.a)!=_io){return new F(function(){return _iF(_iL);});}else{if(E(_iM.b)!=_ip){return new F(function(){return _iF(_iL);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_iN=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_io)==8){if(E(_ip)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_io)==1){if(E(_ip)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_iO=new T(function(){var _iP=function(_iQ){var _iR=E(_iQ),_iS=E(_iR.a),_iT=_iS.b,_iU=E(_iS.a),_iV=function(_iW){return (_iU!=_g8)?true:(E(_iT)!=_hz)?true:(E(_iR.b)==113)?false:true;};if(_iU!=_io){return new F(function(){return _iV(_);});}else{if(E(_iT)!=_ip){return new F(function(){return _iV(_);});}else{return false;}}};return B(_5R(_iP,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_io,_ip),_bv),_iO),b:_5L,c:_iN,d:_ds,e:_iE,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_ih(_im));}));}}}}}}}}}})(_ii));if(_ij!=__continue){return _ij;}}};return new F(function(){return _ih(_g5);});}else{var _iX=B(_4i(_g8,_hz,_ga,_hA));if(!_iX._){return E(_cr);}else{var _iY=E(_iX.b);if(!_iY._){return E(_8I);}else{if(!B(_fE(B(_8D(_iY.a,_iY.b))))){var _iZ=function(_j0){while(1){var _j1=B((function(_j2){var _j3=E(_j2);if(!_j3._){return E(_g3);}else{var _j4=_j3.b,_j5=E(_j3.a),_j6=_g8+E(_j5.a)|0;if(_j6<1){_j0=_j4;return __continue;}else{if(_j6>8){_j0=_j4;return __continue;}else{var _j7=_hz+E(_j5.b)|0;if(_j7<1){_j0=_j4;return __continue;}else{if(_j7>8){_j0=_j4;return __continue;}else{var _j8=B(_4i(_g8,_hz,_j6,_j7));if(!_j8._){return E(_cr);}else{var _j9=E(_j8.b);if(!_j9._){return E(_8I);}else{if(!B(_fE(B(_8D(_j9.a,_j9.b))))){_j0=_j4;return __continue;}else{var _ja=function(_jb){while(1){var _jc=E(_jb);if(!_jc._){return true;}else{var _jd=_jc.b,_je=E(_jc.a),_jf=E(_je.a);if(E(_jf.a)!=_j6){_jb=_jd;continue;}else{if(E(_jf.b)!=_j7){_jb=_jd;continue;}else{var _jg=u_iswupper(E(_je.b));if(!E(_jg)){return false;}else{_jb=_jd;continue;}}}}}};if(!B((function(_jh,_ji){var _jj=E(_jh),_jk=E(_jj.a);if(E(_jk.a)!=_j6){return new F(function(){return _ja(_ji);});}else{if(E(_jk.b)!=_j7){return new F(function(){return _ja(_ji);});}else{var _jl=u_iswupper(E(_jj.b));if(!E(_jl)){return false;}else{return new F(function(){return _ja(_ji);});}}}})(_dC,_dD))){_j0=_j4;return __continue;}else{var _jm=new T(function(){var _jn=function(_jo){while(1){var _jp=E(_jo);if(!_jp._){return false;}else{var _jq=_jp.b,_jr=E(E(_jp.a).a);if(E(_jr.a)!=_j6){_jo=_jq;continue;}else{if(E(_jr.b)!=_j7){_jo=_jq;continue;}else{return true;}}}}};if(!B((function(_js,_jt){var _ju=E(E(_js).a);if(E(_ju.a)!=_j6){return new F(function(){return _jn(_jt);});}else{if(E(_ju.b)!=_j7){return new F(function(){return _jn(_jt);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_jv=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_j6)==8){if(E(_j7)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_j6)==1){if(E(_j7)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_jw=new T(function(){var _jx=function(_jy){var _jz=E(_jy),_jA=E(_jz.a),_jB=_jA.b,_jC=E(_jA.a),_jD=function(_jE){return (_jC!=_g8)?true:(E(_jB)!=_hz)?true:(E(_jz.b)==113)?false:true;};if(_jC!=_j6){return new F(function(){return _jD(_);});}else{if(E(_jB)!=_j7){return new F(function(){return _jD(_);});}else{return false;}}};return B(_5R(_jx,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_j6,_j7),_bv),_jw),b:_5L,c:_jv,d:_ds,e:_jm,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_iZ(_j4));}));}}}}}}}}}})(_j0));if(_j1!=__continue){return _j1;}}};return new F(function(){return _iZ(_g5);});}else{var _jF=function(_jG){while(1){var _jH=E(_jG);if(!_jH._){return true;}else{var _jI=_jH.b,_jJ=E(_jH.a),_jK=E(_jJ.a);if(E(_jK.a)!=_ga){_jG=_jI;continue;}else{if(E(_jK.b)!=_hA){_jG=_jI;continue;}else{var _jL=u_iswupper(E(_jJ.b));if(!E(_jL)){return false;}else{_jG=_jI;continue;}}}}}};if(!B((function(_jM,_jN){var _jO=E(_jM),_jP=E(_jO.a);if(E(_jP.a)!=_ga){return new F(function(){return _jF(_jN);});}else{if(E(_jP.b)!=_hA){return new F(function(){return _jF(_jN);});}else{var _jQ=u_iswupper(E(_jO.b));if(!E(_jQ)){return false;}else{return new F(function(){return _jF(_jN);});}}}})(_dC,_dD))){var _jR=function(_jS){while(1){var _jT=B((function(_jU){var _jV=E(_jU);if(!_jV._){return E(_g3);}else{var _jW=_jV.b,_jX=E(_jV.a),_jY=_g8+E(_jX.a)|0;if(_jY<1){_jS=_jW;return __continue;}else{if(_jY>8){_jS=_jW;return __continue;}else{var _jZ=_hz+E(_jX.b)|0;if(_jZ<1){_jS=_jW;return __continue;}else{if(_jZ>8){_jS=_jW;return __continue;}else{var _k0=B(_4i(_g8,_hz,_jY,_jZ));if(!_k0._){return E(_cr);}else{var _k1=E(_k0.b);if(!_k1._){return E(_8I);}else{if(!B(_fE(B(_8D(_k1.a,_k1.b))))){_jS=_jW;return __continue;}else{var _k2=function(_k3){while(1){var _k4=E(_k3);if(!_k4._){return true;}else{var _k5=_k4.b,_k6=E(_k4.a),_k7=E(_k6.a);if(E(_k7.a)!=_jY){_k3=_k5;continue;}else{if(E(_k7.b)!=_jZ){_k3=_k5;continue;}else{var _k8=u_iswupper(E(_k6.b));if(!E(_k8)){return false;}else{_k3=_k5;continue;}}}}}};if(!B((function(_k9,_ka){var _kb=E(_k9),_kc=E(_kb.a);if(E(_kc.a)!=_jY){return new F(function(){return _k2(_ka);});}else{if(E(_kc.b)!=_jZ){return new F(function(){return _k2(_ka);});}else{var _kd=u_iswupper(E(_kb.b));if(!E(_kd)){return false;}else{return new F(function(){return _k2(_ka);});}}}})(_dC,_dD))){_jS=_jW;return __continue;}else{var _ke=new T(function(){var _kf=function(_kg){while(1){var _kh=E(_kg);if(!_kh._){return false;}else{var _ki=_kh.b,_kj=E(E(_kh.a).a);if(E(_kj.a)!=_jY){_kg=_ki;continue;}else{if(E(_kj.b)!=_jZ){_kg=_ki;continue;}else{return true;}}}}};if(!B((function(_kk,_kl){var _km=E(E(_kk).a);if(E(_km.a)!=_jY){return new F(function(){return _kf(_kl);});}else{if(E(_km.b)!=_jZ){return new F(function(){return _kf(_kl);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_kn=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_jY)==8){if(E(_jZ)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_jY)==1){if(E(_jZ)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_ko=new T(function(){var _kp=function(_kq){var _kr=E(_kq),_ks=E(_kr.a),_kt=_ks.b,_ku=E(_ks.a),_kv=function(_kw){return (_ku!=_g8)?true:(E(_kt)!=_hz)?true:(E(_kr.b)==113)?false:true;};if(_ku!=_jY){return new F(function(){return _kv(_);});}else{if(E(_kt)!=_jZ){return new F(function(){return _kv(_);});}else{return false;}}};return B(_5R(_kp,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_jY,_jZ),_bv),_ko),b:_5L,c:_kn,d:_ds,e:_ke,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_jR(_jW));}));}}}}}}}}}})(_jS));if(_jT!=__continue){return _jT;}}};return new F(function(){return _jR(_g5);});}else{var _kx=new T(function(){var _ky=function(_kz){while(1){var _kA=B((function(_kB){var _kC=E(_kB);if(!_kC._){return E(_g3);}else{var _kD=_kC.b,_kE=E(_kC.a),_kF=_g8+E(_kE.a)|0;if(_kF<1){_kz=_kD;return __continue;}else{if(_kF>8){_kz=_kD;return __continue;}else{var _kG=_hz+E(_kE.b)|0;if(_kG<1){_kz=_kD;return __continue;}else{if(_kG>8){_kz=_kD;return __continue;}else{var _kH=B(_4i(_g8,_hz,_kF,_kG));if(!_kH._){return E(_cr);}else{var _kI=E(_kH.b);if(!_kI._){return E(_8I);}else{if(!B(_fE(B(_8D(_kI.a,_kI.b))))){_kz=_kD;return __continue;}else{var _kJ=function(_kK){while(1){var _kL=E(_kK);if(!_kL._){return true;}else{var _kM=_kL.b,_kN=E(_kL.a),_kO=E(_kN.a);if(E(_kO.a)!=_kF){_kK=_kM;continue;}else{if(E(_kO.b)!=_kG){_kK=_kM;continue;}else{var _kP=u_iswupper(E(_kN.b));if(!E(_kP)){return false;}else{_kK=_kM;continue;}}}}}};if(!B((function(_kQ,_kR){var _kS=E(_kQ),_kT=E(_kS.a);if(E(_kT.a)!=_kF){return new F(function(){return _kJ(_kR);});}else{if(E(_kT.b)!=_kG){return new F(function(){return _kJ(_kR);});}else{var _kU=u_iswupper(E(_kS.b));if(!E(_kU)){return false;}else{return new F(function(){return _kJ(_kR);});}}}})(_dC,_dD))){_kz=_kD;return __continue;}else{var _kV=new T(function(){var _kW=function(_kX){while(1){var _kY=E(_kX);if(!_kY._){return false;}else{var _kZ=_kY.b,_l0=E(E(_kY.a).a);if(E(_l0.a)!=_kF){_kX=_kZ;continue;}else{if(E(_l0.b)!=_kG){_kX=_kZ;continue;}else{return true;}}}}};if(!B((function(_l1,_l2){var _l3=E(E(_l1).a);if(E(_l3.a)!=_kF){return new F(function(){return _kW(_l2);});}else{if(E(_l3.b)!=_kG){return new F(function(){return _kW(_l2);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_l4=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_kF)==8){if(E(_kG)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_kF)==1){if(E(_kG)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_l5=new T(function(){var _l6=function(_l7){var _l8=E(_l7),_l9=E(_l8.a),_la=_l9.b,_lb=E(_l9.a),_lc=function(_ld){return (_lb!=_g8)?true:(E(_la)!=_hz)?true:(E(_l8.b)==113)?false:true;};if(_lb!=_kF){return new F(function(){return _lc(_);});}else{if(E(_la)!=_kG){return new F(function(){return _lc(_);});}else{return false;}}};return B(_5R(_l6,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_kF,_kG),_bv),_l5),b:_5L,c:_l4,d:_ds,e:_kV,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_ky(_kD));}));}}}}}}}}}})(_kz));if(_kA!=__continue){return _kA;}}};return B(_ky(_g5));}),_le=new T(function(){var _lf=function(_lg){while(1){var _lh=E(_lg);if(!_lh._){return false;}else{var _li=_lh.b,_lj=E(E(_lh.a).a);if(E(_lj.a)!=_ga){_lg=_li;continue;}else{if(E(_lj.b)!=_hA){_lg=_li;continue;}else{return true;}}}}};if(!B((function(_lk,_ll){var _lm=E(E(_lk).a);if(E(_lm.a)!=_ga){return new F(function(){return _lf(_ll);});}else{if(E(_lm.b)!=_hA){return new F(function(){return _lf(_ll);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_ln=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_ga)==8){if(E(_hA)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_ga)==1){if(E(_hA)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_lo=new T(function(){var _lp=function(_lq){var _lr=E(_lq),_ls=E(_lr.a),_lt=_ls.b,_lu=E(_ls.a),_lv=function(_lw){return (_lu!=_g8)?true:(E(_lt)!=_hz)?true:(E(_lr.b)==113)?false:true;};if(_lu!=_ga){return new F(function(){return _lv(_);});}else{if(E(_lt)!=_hA){return new F(function(){return _lv(_);});}else{return false;}}};return B(_5R(_lp,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_ga,_hA),_bv),_lo),b:_5L,c:_ln,d:_ds,e:_le,f:_8S,g:_8L,h:_8L,i:_5K},_kx);}}}}}}}}}}else{return E(_g3);}}},_lx=function(_ly,_lz){var _lA=E(_ly),_lB=new T(function(){return B(_fZ(_lz));});if(E(_lA.b)==113){var _lC=E(_bt);if(!_lC._){return E(_lB);}else{var _lD=_lC.b,_lE=E(_lA.a),_lF=_lE.b,_lG=E(_lE.a),_lH=E(_lC.a),_lI=_lG+E(_lH.a)|0;if(_lI<1){var _lJ=function(_lK){while(1){var _lL=B((function(_lM){var _lN=E(_lM);if(!_lN._){return E(_lB);}else{var _lO=_lN.b,_lP=E(_lN.a),_lQ=_lG+E(_lP.a)|0;if(_lQ<1){_lK=_lO;return __continue;}else{if(_lQ>8){_lK=_lO;return __continue;}else{var _lR=E(_lF),_lS=_lR+E(_lP.b)|0;if(_lS<1){_lK=_lO;return __continue;}else{if(_lS>8){_lK=_lO;return __continue;}else{var _lT=B(_4i(_lG,_lR,_lQ,_lS));if(!_lT._){return E(_cr);}else{var _lU=E(_lT.b);if(!_lU._){return E(_8I);}else{if(!B(_fE(B(_8D(_lU.a,_lU.b))))){_lK=_lO;return __continue;}else{var _lV=function(_lW){while(1){var _lX=E(_lW);if(!_lX._){return true;}else{var _lY=_lX.b,_lZ=E(_lX.a),_m0=E(_lZ.a);if(E(_m0.a)!=_lQ){_lW=_lY;continue;}else{if(E(_m0.b)!=_lS){_lW=_lY;continue;}else{var _m1=u_iswupper(E(_lZ.b));if(!E(_m1)){return false;}else{_lW=_lY;continue;}}}}}};if(!B((function(_m2,_m3){var _m4=E(_m2),_m5=E(_m4.a);if(E(_m5.a)!=_lQ){return new F(function(){return _lV(_m3);});}else{if(E(_m5.b)!=_lS){return new F(function(){return _lV(_m3);});}else{var _m6=u_iswupper(E(_m4.b));if(!E(_m6)){return false;}else{return new F(function(){return _lV(_m3);});}}}})(_dC,_dD))){_lK=_lO;return __continue;}else{var _m7=new T(function(){var _m8=function(_m9){while(1){var _ma=E(_m9);if(!_ma._){return false;}else{var _mb=_ma.b,_mc=E(E(_ma.a).a);if(E(_mc.a)!=_lQ){_m9=_mb;continue;}else{if(E(_mc.b)!=_lS){_m9=_mb;continue;}else{return true;}}}}};if(!B((function(_md,_me){var _mf=E(E(_md).a);if(E(_mf.a)!=_lQ){return new F(function(){return _m8(_me);});}else{if(E(_mf.b)!=_lS){return new F(function(){return _m8(_me);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_mg=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_lQ)==8){if(E(_lS)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_lQ)==1){if(E(_lS)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_mh=new T(function(){var _mi=function(_mj){var _mk=E(_mj),_ml=E(_mk.a),_mm=_ml.b,_mn=E(_ml.a),_mo=function(_mp){return (_mn!=_lG)?true:(E(_mm)!=_lR)?true:(E(_mk.b)==113)?false:true;};if(_mn!=_lQ){return new F(function(){return _mo(_);});}else{if(E(_mm)!=_lS){return new F(function(){return _mo(_);});}else{return false;}}};return B(_5R(_mi,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_lQ,_lS),_bv),_mh),b:_5L,c:_mg,d:_ds,e:_m7,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_lJ(_lO));}));}}}}}}}}}})(_lK));if(_lL!=__continue){return _lL;}}};return new F(function(){return _lJ(_lD);});}else{if(_lI>8){var _mq=function(_mr){while(1){var _ms=B((function(_mt){var _mu=E(_mt);if(!_mu._){return E(_lB);}else{var _mv=_mu.b,_mw=E(_mu.a),_mx=_lG+E(_mw.a)|0;if(_mx<1){_mr=_mv;return __continue;}else{if(_mx>8){_mr=_mv;return __continue;}else{var _my=E(_lF),_mz=_my+E(_mw.b)|0;if(_mz<1){_mr=_mv;return __continue;}else{if(_mz>8){_mr=_mv;return __continue;}else{var _mA=B(_4i(_lG,_my,_mx,_mz));if(!_mA._){return E(_cr);}else{var _mB=E(_mA.b);if(!_mB._){return E(_8I);}else{if(!B(_fE(B(_8D(_mB.a,_mB.b))))){_mr=_mv;return __continue;}else{var _mC=function(_mD){while(1){var _mE=E(_mD);if(!_mE._){return true;}else{var _mF=_mE.b,_mG=E(_mE.a),_mH=E(_mG.a);if(E(_mH.a)!=_mx){_mD=_mF;continue;}else{if(E(_mH.b)!=_mz){_mD=_mF;continue;}else{var _mI=u_iswupper(E(_mG.b));if(!E(_mI)){return false;}else{_mD=_mF;continue;}}}}}};if(!B((function(_mJ,_mK){var _mL=E(_mJ),_mM=E(_mL.a);if(E(_mM.a)!=_mx){return new F(function(){return _mC(_mK);});}else{if(E(_mM.b)!=_mz){return new F(function(){return _mC(_mK);});}else{var _mN=u_iswupper(E(_mL.b));if(!E(_mN)){return false;}else{return new F(function(){return _mC(_mK);});}}}})(_dC,_dD))){_mr=_mv;return __continue;}else{var _mO=new T(function(){var _mP=function(_mQ){while(1){var _mR=E(_mQ);if(!_mR._){return false;}else{var _mS=_mR.b,_mT=E(E(_mR.a).a);if(E(_mT.a)!=_mx){_mQ=_mS;continue;}else{if(E(_mT.b)!=_mz){_mQ=_mS;continue;}else{return true;}}}}};if(!B((function(_mU,_mV){var _mW=E(E(_mU).a);if(E(_mW.a)!=_mx){return new F(function(){return _mP(_mV);});}else{if(E(_mW.b)!=_mz){return new F(function(){return _mP(_mV);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_mX=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_mx)==8){if(E(_mz)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_mx)==1){if(E(_mz)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_mY=new T(function(){var _mZ=function(_n0){var _n1=E(_n0),_n2=E(_n1.a),_n3=_n2.b,_n4=E(_n2.a),_n5=function(_n6){return (_n4!=_lG)?true:(E(_n3)!=_my)?true:(E(_n1.b)==113)?false:true;};if(_n4!=_mx){return new F(function(){return _n5(_);});}else{if(E(_n3)!=_mz){return new F(function(){return _n5(_);});}else{return false;}}};return B(_5R(_mZ,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_mx,_mz),_bv),_mY),b:_5L,c:_mX,d:_ds,e:_mO,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_mq(_mv));}));}}}}}}}}}})(_mr));if(_ms!=__continue){return _ms;}}};return new F(function(){return _mq(_lD);});}else{var _n7=E(_lF),_n8=_n7+E(_lH.b)|0;if(_n8<1){var _n9=function(_na){while(1){var _nb=B((function(_nc){var _nd=E(_nc);if(!_nd._){return E(_lB);}else{var _ne=_nd.b,_nf=E(_nd.a),_ng=_lG+E(_nf.a)|0;if(_ng<1){_na=_ne;return __continue;}else{if(_ng>8){_na=_ne;return __continue;}else{var _nh=_n7+E(_nf.b)|0;if(_nh<1){_na=_ne;return __continue;}else{if(_nh>8){_na=_ne;return __continue;}else{var _ni=B(_4i(_lG,_n7,_ng,_nh));if(!_ni._){return E(_cr);}else{var _nj=E(_ni.b);if(!_nj._){return E(_8I);}else{if(!B(_fE(B(_8D(_nj.a,_nj.b))))){_na=_ne;return __continue;}else{var _nk=function(_nl){while(1){var _nm=E(_nl);if(!_nm._){return true;}else{var _nn=_nm.b,_no=E(_nm.a),_np=E(_no.a);if(E(_np.a)!=_ng){_nl=_nn;continue;}else{if(E(_np.b)!=_nh){_nl=_nn;continue;}else{var _nq=u_iswupper(E(_no.b));if(!E(_nq)){return false;}else{_nl=_nn;continue;}}}}}};if(!B((function(_nr,_ns){var _nt=E(_nr),_nu=E(_nt.a);if(E(_nu.a)!=_ng){return new F(function(){return _nk(_ns);});}else{if(E(_nu.b)!=_nh){return new F(function(){return _nk(_ns);});}else{var _nv=u_iswupper(E(_nt.b));if(!E(_nv)){return false;}else{return new F(function(){return _nk(_ns);});}}}})(_dC,_dD))){_na=_ne;return __continue;}else{var _nw=new T(function(){var _nx=function(_ny){while(1){var _nz=E(_ny);if(!_nz._){return false;}else{var _nA=_nz.b,_nB=E(E(_nz.a).a);if(E(_nB.a)!=_ng){_ny=_nA;continue;}else{if(E(_nB.b)!=_nh){_ny=_nA;continue;}else{return true;}}}}};if(!B((function(_nC,_nD){var _nE=E(E(_nC).a);if(E(_nE.a)!=_ng){return new F(function(){return _nx(_nD);});}else{if(E(_nE.b)!=_nh){return new F(function(){return _nx(_nD);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_nF=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_ng)==8){if(E(_nh)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_ng)==1){if(E(_nh)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_nG=new T(function(){var _nH=function(_nI){var _nJ=E(_nI),_nK=E(_nJ.a),_nL=_nK.b,_nM=E(_nK.a),_nN=function(_nO){return (_nM!=_lG)?true:(E(_nL)!=_n7)?true:(E(_nJ.b)==113)?false:true;};if(_nM!=_ng){return new F(function(){return _nN(_);});}else{if(E(_nL)!=_nh){return new F(function(){return _nN(_);});}else{return false;}}};return B(_5R(_nH,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_ng,_nh),_bv),_nG),b:_5L,c:_nF,d:_ds,e:_nw,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_n9(_ne));}));}}}}}}}}}})(_na));if(_nb!=__continue){return _nb;}}};return new F(function(){return _n9(_lD);});}else{if(_n8>8){var _nP=function(_nQ){while(1){var _nR=B((function(_nS){var _nT=E(_nS);if(!_nT._){return E(_lB);}else{var _nU=_nT.b,_nV=E(_nT.a),_nW=_lG+E(_nV.a)|0;if(_nW<1){_nQ=_nU;return __continue;}else{if(_nW>8){_nQ=_nU;return __continue;}else{var _nX=_n7+E(_nV.b)|0;if(_nX<1){_nQ=_nU;return __continue;}else{if(_nX>8){_nQ=_nU;return __continue;}else{var _nY=B(_4i(_lG,_n7,_nW,_nX));if(!_nY._){return E(_cr);}else{var _nZ=E(_nY.b);if(!_nZ._){return E(_8I);}else{if(!B(_fE(B(_8D(_nZ.a,_nZ.b))))){_nQ=_nU;return __continue;}else{var _o0=function(_o1){while(1){var _o2=E(_o1);if(!_o2._){return true;}else{var _o3=_o2.b,_o4=E(_o2.a),_o5=E(_o4.a);if(E(_o5.a)!=_nW){_o1=_o3;continue;}else{if(E(_o5.b)!=_nX){_o1=_o3;continue;}else{var _o6=u_iswupper(E(_o4.b));if(!E(_o6)){return false;}else{_o1=_o3;continue;}}}}}};if(!B((function(_o7,_o8){var _o9=E(_o7),_oa=E(_o9.a);if(E(_oa.a)!=_nW){return new F(function(){return _o0(_o8);});}else{if(E(_oa.b)!=_nX){return new F(function(){return _o0(_o8);});}else{var _ob=u_iswupper(E(_o9.b));if(!E(_ob)){return false;}else{return new F(function(){return _o0(_o8);});}}}})(_dC,_dD))){_nQ=_nU;return __continue;}else{var _oc=new T(function(){var _od=function(_oe){while(1){var _of=E(_oe);if(!_of._){return false;}else{var _og=_of.b,_oh=E(E(_of.a).a);if(E(_oh.a)!=_nW){_oe=_og;continue;}else{if(E(_oh.b)!=_nX){_oe=_og;continue;}else{return true;}}}}};if(!B((function(_oi,_oj){var _ok=E(E(_oi).a);if(E(_ok.a)!=_nW){return new F(function(){return _od(_oj);});}else{if(E(_ok.b)!=_nX){return new F(function(){return _od(_oj);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_ol=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_nW)==8){if(E(_nX)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_nW)==1){if(E(_nX)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_om=new T(function(){var _on=function(_oo){var _op=E(_oo),_oq=E(_op.a),_or=_oq.b,_os=E(_oq.a),_ot=function(_ou){return (_os!=_lG)?true:(E(_or)!=_n7)?true:(E(_op.b)==113)?false:true;};if(_os!=_nW){return new F(function(){return _ot(_);});}else{if(E(_or)!=_nX){return new F(function(){return _ot(_);});}else{return false;}}};return B(_5R(_on,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_nW,_nX),_bv),_om),b:_5L,c:_ol,d:_ds,e:_oc,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_nP(_nU));}));}}}}}}}}}})(_nQ));if(_nR!=__continue){return _nR;}}};return new F(function(){return _nP(_lD);});}else{var _ov=B(_4i(_lG,_n7,_lI,_n8));if(!_ov._){return E(_cr);}else{var _ow=E(_ov.b);if(!_ow._){return E(_8I);}else{if(!B(_fE(B(_8D(_ow.a,_ow.b))))){var _ox=function(_oy){while(1){var _oz=B((function(_oA){var _oB=E(_oA);if(!_oB._){return E(_lB);}else{var _oC=_oB.b,_oD=E(_oB.a),_oE=_lG+E(_oD.a)|0;if(_oE<1){_oy=_oC;return __continue;}else{if(_oE>8){_oy=_oC;return __continue;}else{var _oF=_n7+E(_oD.b)|0;if(_oF<1){_oy=_oC;return __continue;}else{if(_oF>8){_oy=_oC;return __continue;}else{var _oG=B(_4i(_lG,_n7,_oE,_oF));if(!_oG._){return E(_cr);}else{var _oH=E(_oG.b);if(!_oH._){return E(_8I);}else{if(!B(_fE(B(_8D(_oH.a,_oH.b))))){_oy=_oC;return __continue;}else{var _oI=function(_oJ){while(1){var _oK=E(_oJ);if(!_oK._){return true;}else{var _oL=_oK.b,_oM=E(_oK.a),_oN=E(_oM.a);if(E(_oN.a)!=_oE){_oJ=_oL;continue;}else{if(E(_oN.b)!=_oF){_oJ=_oL;continue;}else{var _oO=u_iswupper(E(_oM.b));if(!E(_oO)){return false;}else{_oJ=_oL;continue;}}}}}};if(!B((function(_oP,_oQ){var _oR=E(_oP),_oS=E(_oR.a);if(E(_oS.a)!=_oE){return new F(function(){return _oI(_oQ);});}else{if(E(_oS.b)!=_oF){return new F(function(){return _oI(_oQ);});}else{var _oT=u_iswupper(E(_oR.b));if(!E(_oT)){return false;}else{return new F(function(){return _oI(_oQ);});}}}})(_dC,_dD))){_oy=_oC;return __continue;}else{var _oU=new T(function(){var _oV=function(_oW){while(1){var _oX=E(_oW);if(!_oX._){return false;}else{var _oY=_oX.b,_oZ=E(E(_oX.a).a);if(E(_oZ.a)!=_oE){_oW=_oY;continue;}else{if(E(_oZ.b)!=_oF){_oW=_oY;continue;}else{return true;}}}}};if(!B((function(_p0,_p1){var _p2=E(E(_p0).a);if(E(_p2.a)!=_oE){return new F(function(){return _oV(_p1);});}else{if(E(_p2.b)!=_oF){return new F(function(){return _oV(_p1);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_p3=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_oE)==8){if(E(_oF)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_oE)==1){if(E(_oF)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_p4=new T(function(){var _p5=function(_p6){var _p7=E(_p6),_p8=E(_p7.a),_p9=_p8.b,_pa=E(_p8.a),_pb=function(_pc){return (_pa!=_lG)?true:(E(_p9)!=_n7)?true:(E(_p7.b)==113)?false:true;};if(_pa!=_oE){return new F(function(){return _pb(_);});}else{if(E(_p9)!=_oF){return new F(function(){return _pb(_);});}else{return false;}}};return B(_5R(_p5,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_oE,_oF),_bv),_p4),b:_5L,c:_p3,d:_ds,e:_oU,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_ox(_oC));}));}}}}}}}}}})(_oy));if(_oz!=__continue){return _oz;}}};return new F(function(){return _ox(_lD);});}else{var _pd=function(_pe){while(1){var _pf=E(_pe);if(!_pf._){return true;}else{var _pg=_pf.b,_ph=E(_pf.a),_pi=E(_ph.a);if(E(_pi.a)!=_lI){_pe=_pg;continue;}else{if(E(_pi.b)!=_n8){_pe=_pg;continue;}else{var _pj=u_iswupper(E(_ph.b));if(!E(_pj)){return false;}else{_pe=_pg;continue;}}}}}};if(!B((function(_pk,_pl){var _pm=E(_pk),_pn=E(_pm.a);if(E(_pn.a)!=_lI){return new F(function(){return _pd(_pl);});}else{if(E(_pn.b)!=_n8){return new F(function(){return _pd(_pl);});}else{var _po=u_iswupper(E(_pm.b));if(!E(_po)){return false;}else{return new F(function(){return _pd(_pl);});}}}})(_dC,_dD))){var _pp=function(_pq){while(1){var _pr=B((function(_ps){var _pt=E(_ps);if(!_pt._){return E(_lB);}else{var _pu=_pt.b,_pv=E(_pt.a),_pw=_lG+E(_pv.a)|0;if(_pw<1){_pq=_pu;return __continue;}else{if(_pw>8){_pq=_pu;return __continue;}else{var _px=_n7+E(_pv.b)|0;if(_px<1){_pq=_pu;return __continue;}else{if(_px>8){_pq=_pu;return __continue;}else{var _py=B(_4i(_lG,_n7,_pw,_px));if(!_py._){return E(_cr);}else{var _pz=E(_py.b);if(!_pz._){return E(_8I);}else{if(!B(_fE(B(_8D(_pz.a,_pz.b))))){_pq=_pu;return __continue;}else{var _pA=function(_pB){while(1){var _pC=E(_pB);if(!_pC._){return true;}else{var _pD=_pC.b,_pE=E(_pC.a),_pF=E(_pE.a);if(E(_pF.a)!=_pw){_pB=_pD;continue;}else{if(E(_pF.b)!=_px){_pB=_pD;continue;}else{var _pG=u_iswupper(E(_pE.b));if(!E(_pG)){return false;}else{_pB=_pD;continue;}}}}}};if(!B((function(_pH,_pI){var _pJ=E(_pH),_pK=E(_pJ.a);if(E(_pK.a)!=_pw){return new F(function(){return _pA(_pI);});}else{if(E(_pK.b)!=_px){return new F(function(){return _pA(_pI);});}else{var _pL=u_iswupper(E(_pJ.b));if(!E(_pL)){return false;}else{return new F(function(){return _pA(_pI);});}}}})(_dC,_dD))){_pq=_pu;return __continue;}else{var _pM=new T(function(){var _pN=function(_pO){while(1){var _pP=E(_pO);if(!_pP._){return false;}else{var _pQ=_pP.b,_pR=E(E(_pP.a).a);if(E(_pR.a)!=_pw){_pO=_pQ;continue;}else{if(E(_pR.b)!=_px){_pO=_pQ;continue;}else{return true;}}}}};if(!B((function(_pS,_pT){var _pU=E(E(_pS).a);if(E(_pU.a)!=_pw){return new F(function(){return _pN(_pT);});}else{if(E(_pU.b)!=_px){return new F(function(){return _pN(_pT);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_pV=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_pw)==8){if(E(_px)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_pw)==1){if(E(_px)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_pW=new T(function(){var _pX=function(_pY){var _pZ=E(_pY),_q0=E(_pZ.a),_q1=_q0.b,_q2=E(_q0.a),_q3=function(_q4){return (_q2!=_lG)?true:(E(_q1)!=_n7)?true:(E(_pZ.b)==113)?false:true;};if(_q2!=_pw){return new F(function(){return _q3(_);});}else{if(E(_q1)!=_px){return new F(function(){return _q3(_);});}else{return false;}}};return B(_5R(_pX,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_pw,_px),_bv),_pW),b:_5L,c:_pV,d:_ds,e:_pM,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_pp(_pu));}));}}}}}}}}}})(_pq));if(_pr!=__continue){return _pr;}}};return new F(function(){return _pp(_lD);});}else{var _q5=new T(function(){var _q6=function(_q7){while(1){var _q8=B((function(_q9){var _qa=E(_q9);if(!_qa._){return E(_lB);}else{var _qb=_qa.b,_qc=E(_qa.a),_qd=_lG+E(_qc.a)|0;if(_qd<1){_q7=_qb;return __continue;}else{if(_qd>8){_q7=_qb;return __continue;}else{var _qe=_n7+E(_qc.b)|0;if(_qe<1){_q7=_qb;return __continue;}else{if(_qe>8){_q7=_qb;return __continue;}else{var _qf=B(_4i(_lG,_n7,_qd,_qe));if(!_qf._){return E(_cr);}else{var _qg=E(_qf.b);if(!_qg._){return E(_8I);}else{if(!B(_fE(B(_8D(_qg.a,_qg.b))))){_q7=_qb;return __continue;}else{var _qh=function(_qi){while(1){var _qj=E(_qi);if(!_qj._){return true;}else{var _qk=_qj.b,_ql=E(_qj.a),_qm=E(_ql.a);if(E(_qm.a)!=_qd){_qi=_qk;continue;}else{if(E(_qm.b)!=_qe){_qi=_qk;continue;}else{var _qn=u_iswupper(E(_ql.b));if(!E(_qn)){return false;}else{_qi=_qk;continue;}}}}}};if(!B((function(_qo,_qp){var _qq=E(_qo),_qr=E(_qq.a);if(E(_qr.a)!=_qd){return new F(function(){return _qh(_qp);});}else{if(E(_qr.b)!=_qe){return new F(function(){return _qh(_qp);});}else{var _qs=u_iswupper(E(_qq.b));if(!E(_qs)){return false;}else{return new F(function(){return _qh(_qp);});}}}})(_dC,_dD))){_q7=_qb;return __continue;}else{var _qt=new T(function(){var _qu=function(_qv){while(1){var _qw=E(_qv);if(!_qw._){return false;}else{var _qx=_qw.b,_qy=E(E(_qw.a).a);if(E(_qy.a)!=_qd){_qv=_qx;continue;}else{if(E(_qy.b)!=_qe){_qv=_qx;continue;}else{return true;}}}}};if(!B((function(_qz,_qA){var _qB=E(E(_qz).a);if(E(_qB.a)!=_qd){return new F(function(){return _qu(_qA);});}else{if(E(_qB.b)!=_qe){return new F(function(){return _qu(_qA);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_qC=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_qd)==8){if(E(_qe)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_qd)==1){if(E(_qe)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_qD=new T(function(){var _qE=function(_qF){var _qG=E(_qF),_qH=E(_qG.a),_qI=_qH.b,_qJ=E(_qH.a),_qK=function(_qL){return (_qJ!=_lG)?true:(E(_qI)!=_n7)?true:(E(_qG.b)==113)?false:true;};if(_qJ!=_qd){return new F(function(){return _qK(_);});}else{if(E(_qI)!=_qe){return new F(function(){return _qK(_);});}else{return false;}}};return B(_5R(_qE,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_qd,_qe),_bv),_qD),b:_5L,c:_qC,d:_ds,e:_qt,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_q6(_qb));}));}}}}}}}}}})(_q7));if(_q8!=__continue){return _q8;}}};return B(_q6(_lD));}),_qM=new T(function(){var _qN=function(_qO){while(1){var _qP=E(_qO);if(!_qP._){return false;}else{var _qQ=_qP.b,_qR=E(E(_qP.a).a);if(E(_qR.a)!=_lI){_qO=_qQ;continue;}else{if(E(_qR.b)!=_n8){_qO=_qQ;continue;}else{return true;}}}}};if(!B((function(_qS,_qT){var _qU=E(E(_qS).a);if(E(_qU.a)!=_lI){return new F(function(){return _qN(_qT);});}else{if(E(_qU.b)!=_n8){return new F(function(){return _qN(_qT);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_qV=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_lI)==8){if(E(_n8)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_lI)==1){if(E(_n8)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_qW=new T(function(){var _qX=function(_qY){var _qZ=E(_qY),_r0=E(_qZ.a),_r1=_r0.b,_r2=E(_r0.a),_r3=function(_r4){return (_r2!=_lG)?true:(E(_r1)!=_n7)?true:(E(_qZ.b)==113)?false:true;};if(_r2!=_lI){return new F(function(){return _r3(_);});}else{if(E(_r1)!=_n8){return new F(function(){return _r3(_);});}else{return false;}}};return B(_5R(_qX,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_lI,_n8),_bv),_qW),b:_5L,c:_qV,d:_ds,e:_qM,f:_8S,g:_8L,h:_8L,i:_5K},_q5);}}}}}}}}}}else{return E(_lB);}};return B(_lx(_dC,_dD));}),_r5=function(_r6){while(1){var _r7=B((function(_r8){var _r9=E(_r8);if(!_r9._){return E(_eQ);}else{var _ra=_r9.b,_rb=E(_r9.a);if(E(_rb.b)==110){var _rc=function(_rd,_re,_rf){var _rg=E(_rb.a),_rh=E(_rg.a),_ri=_rh+_rd|0;if(_ri<1){return E(_rf);}else{if(_ri>8){return E(_rf);}else{var _rj=E(_rg.b),_rk=_rj+_re|0;if(_rk<1){return E(_rf);}else{if(_rk>8){return E(_rf);}else{var _rl=function(_rm){while(1){var _rn=E(_rm);if(!_rn._){return true;}else{var _ro=_rn.b,_rp=E(_rn.a),_rq=E(_rp.a);if(E(_rq.a)!=_ri){_rm=_ro;continue;}else{if(E(_rq.b)!=_rk){_rm=_ro;continue;}else{var _rr=u_iswupper(E(_rp.b));if(!E(_rr)){return false;}else{_rm=_ro;continue;}}}}}};if(!B((function(_rs,_rt){var _ru=E(_rs),_rv=E(_ru.a);if(E(_rv.a)!=_ri){return new F(function(){return _rl(_rt);});}else{if(E(_rv.b)!=_rk){return new F(function(){return _rl(_rt);});}else{var _rw=u_iswupper(E(_ru.b));if(!E(_rw)){return false;}else{return new F(function(){return _rl(_rt);});}}}})(_dC,_dD))){return E(_rf);}else{var _rx=new T(function(){var _ry=function(_rz){while(1){var _rA=E(_rz);if(!_rA._){return false;}else{var _rB=_rA.b,_rC=E(E(_rA.a).a);if(E(_rC.a)!=_ri){_rz=_rB;continue;}else{if(E(_rC.b)!=_rk){_rz=_rB;continue;}else{return true;}}}}};if(!B((function(_rD,_rE){var _rF=E(E(_rD).a);if(E(_rF.a)!=_ri){return new F(function(){return _ry(_rE);});}else{if(E(_rF.b)!=_rk){return new F(function(){return _ry(_rE);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_rG=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_ri)==8){if(E(_rk)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_ri)==1){if(E(_rk)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_rH=new T(function(){var _rI=function(_rJ){var _rK=E(_rJ),_rL=E(_rK.a),_rM=_rL.b,_rN=E(_rL.a),_rO=function(_rP){return (_rN!=_rh)?true:(E(_rM)!=_rj)?true:(E(_rK.b)==110)?false:true;};if(_rN!=_ri){return new F(function(){return _rO(_);});}else{if(E(_rM)!=_rk){return new F(function(){return _rO(_);});}else{return false;}}};return B(_5R(_rI,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_ri,_rk),_bw),_rH),b:_5L,c:_rG,d:_ds,e:_rx,f:_8S,g:_8L,h:_8L,i:_5K},_rf);}}}}}},_rQ=new T(function(){var _rR=new T(function(){var _rS=new T(function(){var _rT=new T(function(){var _rU=new T(function(){var _rV=new T(function(){var _rW=new T(function(){return B(_rc(-2,-1,new T(function(){return B(_r5(_ra));})));});return B(_rc(-1,-2,_rW));});return B(_rc(2,-1,_rV));});return B(_rc(-1,2,_rU));});return B(_rc(-2,1,_rT));});return B(_rc(1,-2,_rS));});return B(_rc(2,1,_rR));});return new F(function(){return _rc(1,2,_rQ);});}else{_r6=_ra;return __continue;}}})(_r6));if(_r7!=__continue){return _r7;}}},_rX=function(_rY,_rZ){var _s0=E(_rY);if(E(_s0.b)==110){var _s1=function(_s2,_s3,_s4){var _s5=E(_s0.a),_s6=E(_s5.a),_s7=_s6+_s2|0;if(_s7<1){return E(_s4);}else{if(_s7>8){return E(_s4);}else{var _s8=E(_s5.b),_s9=_s8+_s3|0;if(_s9<1){return E(_s4);}else{if(_s9>8){return E(_s4);}else{var _sa=function(_sb){while(1){var _sc=E(_sb);if(!_sc._){return true;}else{var _sd=_sc.b,_se=E(_sc.a),_sf=E(_se.a);if(E(_sf.a)!=_s7){_sb=_sd;continue;}else{if(E(_sf.b)!=_s9){_sb=_sd;continue;}else{var _sg=u_iswupper(E(_se.b));if(!E(_sg)){return false;}else{_sb=_sd;continue;}}}}}};if(!B(_sa(_dB))){return E(_s4);}else{var _sh=new T(function(){var _si=function(_sj){while(1){var _sk=E(_sj);if(!_sk._){return false;}else{var _sl=_sk.b,_sm=E(E(_sk.a).a);if(E(_sm.a)!=_s7){_sj=_sl;continue;}else{if(E(_sm.b)!=_s9){_sj=_sl;continue;}else{return true;}}}}};if(!B(_si(_dB))){return E(_8M);}else{return E(_8U);}}),_sn=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_s7)==8){if(E(_s9)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_s7)==1){if(E(_s9)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_so=new T(function(){var _sp=function(_sq){var _sr=E(_sq),_ss=E(_sr.a),_st=_ss.b,_su=E(_ss.a),_sv=function(_sw){return (_su!=_s6)?true:(E(_st)!=_s8)?true:(E(_sr.b)==110)?false:true;};if(_su!=_s7){return new F(function(){return _sv(_);});}else{if(E(_st)!=_s9){return new F(function(){return _sv(_);});}else{return false;}}};return B(_5R(_sp,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_s7,_s9),_bw),_so),b:_5L,c:_sn,d:_ds,e:_sh,f:_8S,g:_8L,h:_8L,i:_5K},_s4);}}}}}},_sx=new T(function(){var _sy=new T(function(){var _sz=new T(function(){var _sA=new T(function(){var _sB=new T(function(){var _sC=new T(function(){var _sD=new T(function(){return B(_s1(-2,-1,new T(function(){return B(_r5(_rZ));})));});return B(_s1(-1,-2,_sD));});return B(_s1(2,-1,_sC));});return B(_s1(-1,2,_sB));});return B(_s1(-2,1,_sA));});return B(_s1(1,-2,_sz));});return B(_s1(2,1,_sy));});return new F(function(){return _s1(1,2,_sx);});}else{return new F(function(){return _r5(_rZ);});}};return B(_rX(_dC,_dD));}),_sE=function(_sF){while(1){var _sG=B((function(_sH){var _sI=E(_sH);if(!_sI._){return true;}else{var _sJ=_sI.b,_sK=E(E(_dC).a),_sL=E(_sI.a),_sM=_sL.b,_sN=E(_sL.a);if(E(_sK.a)!=_sN){var _sO=function(_sP){while(1){var _sQ=E(_sP);if(!_sQ._){return true;}else{var _sR=_sQ.b,_sS=E(E(_sQ.a).a);if(E(_sS.a)!=_sN){_sP=_sR;continue;}else{if(E(_sS.b)!=E(_sM)){_sP=_sR;continue;}else{return false;}}}}};if(!B(_sO(_dD))){return false;}else{_sF=_sJ;return __continue;}}else{var _sT=E(_sM);if(E(_sK.b)!=_sT){var _sU=function(_sV){while(1){var _sW=E(_sV);if(!_sW._){return true;}else{var _sX=_sW.b,_sY=E(E(_sW.a).a);if(E(_sY.a)!=_sN){_sV=_sX;continue;}else{if(E(_sY.b)!=_sT){_sV=_sX;continue;}else{return false;}}}}};if(!B(_sU(_dD))){return false;}else{_sF=_sJ;return __continue;}}else{return false;}}}})(_sF));if(_sG!=__continue){return _sG;}}},_sZ=function(_t0){var _t1=E(_t0);if(!_t1._){return E(_eP);}else{var _t2=E(_t1.a),_t3=new T(function(){return B(_sZ(_t1.b));});if(E(_t2.b)==98){var _t4=E(_bN);if(!_t4._){return E(_t3);}else{var _t5=_t4.b,_t6=E(_t2.a),_t7=_t6.b,_t8=E(_t6.a),_t9=E(_t4.a),_ta=_t8+E(_t9.a)|0;if(_ta<1){var _tb=function(_tc){while(1){var _td=B((function(_te){var _tf=E(_te);if(!_tf._){return E(_t3);}else{var _tg=_tf.b,_th=E(_tf.a),_ti=_t8+E(_th.a)|0;if(_ti<1){_tc=_tg;return __continue;}else{if(_ti>8){_tc=_tg;return __continue;}else{var _tj=E(_t7),_tk=_tj+E(_th.b)|0;if(_tk<1){_tc=_tg;return __continue;}else{if(_tk>8){_tc=_tg;return __continue;}else{var _tl=B(_4i(_t8,_tj,_ti,_tk));if(!_tl._){return E(_cr);}else{var _tm=E(_tl.b);if(!_tm._){return E(_8I);}else{if(!B(_sE(B(_8D(_tm.a,_tm.b))))){_tc=_tg;return __continue;}else{var _tn=function(_to){while(1){var _tp=E(_to);if(!_tp._){return true;}else{var _tq=_tp.b,_tr=E(_tp.a),_ts=E(_tr.a);if(E(_ts.a)!=_ti){_to=_tq;continue;}else{if(E(_ts.b)!=_tk){_to=_tq;continue;}else{var _tt=u_iswupper(E(_tr.b));if(!E(_tt)){return false;}else{_to=_tq;continue;}}}}}};if(!B((function(_tu,_tv){var _tw=E(_tu),_tx=E(_tw.a);if(E(_tx.a)!=_ti){return new F(function(){return _tn(_tv);});}else{if(E(_tx.b)!=_tk){return new F(function(){return _tn(_tv);});}else{var _ty=u_iswupper(E(_tw.b));if(!E(_ty)){return false;}else{return new F(function(){return _tn(_tv);});}}}})(_dC,_dD))){_tc=_tg;return __continue;}else{var _tz=new T(function(){var _tA=function(_tB){while(1){var _tC=E(_tB);if(!_tC._){return false;}else{var _tD=_tC.b,_tE=E(E(_tC.a).a);if(E(_tE.a)!=_ti){_tB=_tD;continue;}else{if(E(_tE.b)!=_tk){_tB=_tD;continue;}else{return true;}}}}};if(!B((function(_tF,_tG){var _tH=E(E(_tF).a);if(E(_tH.a)!=_ti){return new F(function(){return _tA(_tG);});}else{if(E(_tH.b)!=_tk){return new F(function(){return _tA(_tG);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_tI=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_ti)==8){if(E(_tk)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_ti)==1){if(E(_tk)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_tJ=new T(function(){var _tK=function(_tL){var _tM=E(_tL),_tN=E(_tM.a),_tO=_tN.b,_tP=E(_tN.a),_tQ=function(_tR){return (_tP!=_t8)?true:(E(_tO)!=_tj)?true:(E(_tM.b)==98)?false:true;};if(_tP!=_ti){return new F(function(){return _tQ(_);});}else{if(E(_tO)!=_tk){return new F(function(){return _tQ(_);});}else{return false;}}};return B(_5R(_tK,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_ti,_tk),_bP),_tJ),b:_5L,c:_tI,d:_ds,e:_tz,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_tb(_tg));}));}}}}}}}}}})(_tc));if(_td!=__continue){return _td;}}};return new F(function(){return _tb(_t5);});}else{if(_ta>8){var _tS=function(_tT){while(1){var _tU=B((function(_tV){var _tW=E(_tV);if(!_tW._){return E(_t3);}else{var _tX=_tW.b,_tY=E(_tW.a),_tZ=_t8+E(_tY.a)|0;if(_tZ<1){_tT=_tX;return __continue;}else{if(_tZ>8){_tT=_tX;return __continue;}else{var _u0=E(_t7),_u1=_u0+E(_tY.b)|0;if(_u1<1){_tT=_tX;return __continue;}else{if(_u1>8){_tT=_tX;return __continue;}else{var _u2=B(_4i(_t8,_u0,_tZ,_u1));if(!_u2._){return E(_cr);}else{var _u3=E(_u2.b);if(!_u3._){return E(_8I);}else{if(!B(_sE(B(_8D(_u3.a,_u3.b))))){_tT=_tX;return __continue;}else{var _u4=function(_u5){while(1){var _u6=E(_u5);if(!_u6._){return true;}else{var _u7=_u6.b,_u8=E(_u6.a),_u9=E(_u8.a);if(E(_u9.a)!=_tZ){_u5=_u7;continue;}else{if(E(_u9.b)!=_u1){_u5=_u7;continue;}else{var _ua=u_iswupper(E(_u8.b));if(!E(_ua)){return false;}else{_u5=_u7;continue;}}}}}};if(!B((function(_ub,_uc){var _ud=E(_ub),_ue=E(_ud.a);if(E(_ue.a)!=_tZ){return new F(function(){return _u4(_uc);});}else{if(E(_ue.b)!=_u1){return new F(function(){return _u4(_uc);});}else{var _uf=u_iswupper(E(_ud.b));if(!E(_uf)){return false;}else{return new F(function(){return _u4(_uc);});}}}})(_dC,_dD))){_tT=_tX;return __continue;}else{var _ug=new T(function(){var _uh=function(_ui){while(1){var _uj=E(_ui);if(!_uj._){return false;}else{var _uk=_uj.b,_ul=E(E(_uj.a).a);if(E(_ul.a)!=_tZ){_ui=_uk;continue;}else{if(E(_ul.b)!=_u1){_ui=_uk;continue;}else{return true;}}}}};if(!B((function(_um,_un){var _uo=E(E(_um).a);if(E(_uo.a)!=_tZ){return new F(function(){return _uh(_un);});}else{if(E(_uo.b)!=_u1){return new F(function(){return _uh(_un);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_up=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_tZ)==8){if(E(_u1)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_tZ)==1){if(E(_u1)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_uq=new T(function(){var _ur=function(_us){var _ut=E(_us),_uu=E(_ut.a),_uv=_uu.b,_uw=E(_uu.a),_ux=function(_uy){return (_uw!=_t8)?true:(E(_uv)!=_u0)?true:(E(_ut.b)==98)?false:true;};if(_uw!=_tZ){return new F(function(){return _ux(_);});}else{if(E(_uv)!=_u1){return new F(function(){return _ux(_);});}else{return false;}}};return B(_5R(_ur,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_tZ,_u1),_bP),_uq),b:_5L,c:_up,d:_ds,e:_ug,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_tS(_tX));}));}}}}}}}}}})(_tT));if(_tU!=__continue){return _tU;}}};return new F(function(){return _tS(_t5);});}else{var _uz=E(_t7),_uA=_uz+E(_t9.b)|0;if(_uA<1){var _uB=function(_uC){while(1){var _uD=B((function(_uE){var _uF=E(_uE);if(!_uF._){return E(_t3);}else{var _uG=_uF.b,_uH=E(_uF.a),_uI=_t8+E(_uH.a)|0;if(_uI<1){_uC=_uG;return __continue;}else{if(_uI>8){_uC=_uG;return __continue;}else{var _uJ=_uz+E(_uH.b)|0;if(_uJ<1){_uC=_uG;return __continue;}else{if(_uJ>8){_uC=_uG;return __continue;}else{var _uK=B(_4i(_t8,_uz,_uI,_uJ));if(!_uK._){return E(_cr);}else{var _uL=E(_uK.b);if(!_uL._){return E(_8I);}else{if(!B(_sE(B(_8D(_uL.a,_uL.b))))){_uC=_uG;return __continue;}else{var _uM=function(_uN){while(1){var _uO=E(_uN);if(!_uO._){return true;}else{var _uP=_uO.b,_uQ=E(_uO.a),_uR=E(_uQ.a);if(E(_uR.a)!=_uI){_uN=_uP;continue;}else{if(E(_uR.b)!=_uJ){_uN=_uP;continue;}else{var _uS=u_iswupper(E(_uQ.b));if(!E(_uS)){return false;}else{_uN=_uP;continue;}}}}}};if(!B((function(_uT,_uU){var _uV=E(_uT),_uW=E(_uV.a);if(E(_uW.a)!=_uI){return new F(function(){return _uM(_uU);});}else{if(E(_uW.b)!=_uJ){return new F(function(){return _uM(_uU);});}else{var _uX=u_iswupper(E(_uV.b));if(!E(_uX)){return false;}else{return new F(function(){return _uM(_uU);});}}}})(_dC,_dD))){_uC=_uG;return __continue;}else{var _uY=new T(function(){var _uZ=function(_v0){while(1){var _v1=E(_v0);if(!_v1._){return false;}else{var _v2=_v1.b,_v3=E(E(_v1.a).a);if(E(_v3.a)!=_uI){_v0=_v2;continue;}else{if(E(_v3.b)!=_uJ){_v0=_v2;continue;}else{return true;}}}}};if(!B((function(_v4,_v5){var _v6=E(E(_v4).a);if(E(_v6.a)!=_uI){return new F(function(){return _uZ(_v5);});}else{if(E(_v6.b)!=_uJ){return new F(function(){return _uZ(_v5);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_v7=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_uI)==8){if(E(_uJ)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_uI)==1){if(E(_uJ)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_v8=new T(function(){var _v9=function(_va){var _vb=E(_va),_vc=E(_vb.a),_vd=_vc.b,_ve=E(_vc.a),_vf=function(_vg){return (_ve!=_t8)?true:(E(_vd)!=_uz)?true:(E(_vb.b)==98)?false:true;};if(_ve!=_uI){return new F(function(){return _vf(_);});}else{if(E(_vd)!=_uJ){return new F(function(){return _vf(_);});}else{return false;}}};return B(_5R(_v9,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_uI,_uJ),_bP),_v8),b:_5L,c:_v7,d:_ds,e:_uY,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_uB(_uG));}));}}}}}}}}}})(_uC));if(_uD!=__continue){return _uD;}}};return new F(function(){return _uB(_t5);});}else{if(_uA>8){var _vh=function(_vi){while(1){var _vj=B((function(_vk){var _vl=E(_vk);if(!_vl._){return E(_t3);}else{var _vm=_vl.b,_vn=E(_vl.a),_vo=_t8+E(_vn.a)|0;if(_vo<1){_vi=_vm;return __continue;}else{if(_vo>8){_vi=_vm;return __continue;}else{var _vp=_uz+E(_vn.b)|0;if(_vp<1){_vi=_vm;return __continue;}else{if(_vp>8){_vi=_vm;return __continue;}else{var _vq=B(_4i(_t8,_uz,_vo,_vp));if(!_vq._){return E(_cr);}else{var _vr=E(_vq.b);if(!_vr._){return E(_8I);}else{if(!B(_sE(B(_8D(_vr.a,_vr.b))))){_vi=_vm;return __continue;}else{var _vs=function(_vt){while(1){var _vu=E(_vt);if(!_vu._){return true;}else{var _vv=_vu.b,_vw=E(_vu.a),_vx=E(_vw.a);if(E(_vx.a)!=_vo){_vt=_vv;continue;}else{if(E(_vx.b)!=_vp){_vt=_vv;continue;}else{var _vy=u_iswupper(E(_vw.b));if(!E(_vy)){return false;}else{_vt=_vv;continue;}}}}}};if(!B((function(_vz,_vA){var _vB=E(_vz),_vC=E(_vB.a);if(E(_vC.a)!=_vo){return new F(function(){return _vs(_vA);});}else{if(E(_vC.b)!=_vp){return new F(function(){return _vs(_vA);});}else{var _vD=u_iswupper(E(_vB.b));if(!E(_vD)){return false;}else{return new F(function(){return _vs(_vA);});}}}})(_dC,_dD))){_vi=_vm;return __continue;}else{var _vE=new T(function(){var _vF=function(_vG){while(1){var _vH=E(_vG);if(!_vH._){return false;}else{var _vI=_vH.b,_vJ=E(E(_vH.a).a);if(E(_vJ.a)!=_vo){_vG=_vI;continue;}else{if(E(_vJ.b)!=_vp){_vG=_vI;continue;}else{return true;}}}}};if(!B((function(_vK,_vL){var _vM=E(E(_vK).a);if(E(_vM.a)!=_vo){return new F(function(){return _vF(_vL);});}else{if(E(_vM.b)!=_vp){return new F(function(){return _vF(_vL);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_vN=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_vo)==8){if(E(_vp)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_vo)==1){if(E(_vp)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_vO=new T(function(){var _vP=function(_vQ){var _vR=E(_vQ),_vS=E(_vR.a),_vT=_vS.b,_vU=E(_vS.a),_vV=function(_vW){return (_vU!=_t8)?true:(E(_vT)!=_uz)?true:(E(_vR.b)==98)?false:true;};if(_vU!=_vo){return new F(function(){return _vV(_);});}else{if(E(_vT)!=_vp){return new F(function(){return _vV(_);});}else{return false;}}};return B(_5R(_vP,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_vo,_vp),_bP),_vO),b:_5L,c:_vN,d:_ds,e:_vE,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_vh(_vm));}));}}}}}}}}}})(_vi));if(_vj!=__continue){return _vj;}}};return new F(function(){return _vh(_t5);});}else{var _vX=B(_4i(_t8,_uz,_ta,_uA));if(!_vX._){return E(_cr);}else{var _vY=E(_vX.b);if(!_vY._){return E(_8I);}else{if(!B(_sE(B(_8D(_vY.a,_vY.b))))){var _vZ=function(_w0){while(1){var _w1=B((function(_w2){var _w3=E(_w2);if(!_w3._){return E(_t3);}else{var _w4=_w3.b,_w5=E(_w3.a),_w6=_t8+E(_w5.a)|0;if(_w6<1){_w0=_w4;return __continue;}else{if(_w6>8){_w0=_w4;return __continue;}else{var _w7=_uz+E(_w5.b)|0;if(_w7<1){_w0=_w4;return __continue;}else{if(_w7>8){_w0=_w4;return __continue;}else{var _w8=B(_4i(_t8,_uz,_w6,_w7));if(!_w8._){return E(_cr);}else{var _w9=E(_w8.b);if(!_w9._){return E(_8I);}else{if(!B(_sE(B(_8D(_w9.a,_w9.b))))){_w0=_w4;return __continue;}else{var _wa=function(_wb){while(1){var _wc=E(_wb);if(!_wc._){return true;}else{var _wd=_wc.b,_we=E(_wc.a),_wf=E(_we.a);if(E(_wf.a)!=_w6){_wb=_wd;continue;}else{if(E(_wf.b)!=_w7){_wb=_wd;continue;}else{var _wg=u_iswupper(E(_we.b));if(!E(_wg)){return false;}else{_wb=_wd;continue;}}}}}};if(!B((function(_wh,_wi){var _wj=E(_wh),_wk=E(_wj.a);if(E(_wk.a)!=_w6){return new F(function(){return _wa(_wi);});}else{if(E(_wk.b)!=_w7){return new F(function(){return _wa(_wi);});}else{var _wl=u_iswupper(E(_wj.b));if(!E(_wl)){return false;}else{return new F(function(){return _wa(_wi);});}}}})(_dC,_dD))){_w0=_w4;return __continue;}else{var _wm=new T(function(){var _wn=function(_wo){while(1){var _wp=E(_wo);if(!_wp._){return false;}else{var _wq=_wp.b,_wr=E(E(_wp.a).a);if(E(_wr.a)!=_w6){_wo=_wq;continue;}else{if(E(_wr.b)!=_w7){_wo=_wq;continue;}else{return true;}}}}};if(!B((function(_ws,_wt){var _wu=E(E(_ws).a);if(E(_wu.a)!=_w6){return new F(function(){return _wn(_wt);});}else{if(E(_wu.b)!=_w7){return new F(function(){return _wn(_wt);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_wv=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_w6)==8){if(E(_w7)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_w6)==1){if(E(_w7)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_ww=new T(function(){var _wx=function(_wy){var _wz=E(_wy),_wA=E(_wz.a),_wB=_wA.b,_wC=E(_wA.a),_wD=function(_wE){return (_wC!=_t8)?true:(E(_wB)!=_uz)?true:(E(_wz.b)==98)?false:true;};if(_wC!=_w6){return new F(function(){return _wD(_);});}else{if(E(_wB)!=_w7){return new F(function(){return _wD(_);});}else{return false;}}};return B(_5R(_wx,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_w6,_w7),_bP),_ww),b:_5L,c:_wv,d:_ds,e:_wm,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_vZ(_w4));}));}}}}}}}}}})(_w0));if(_w1!=__continue){return _w1;}}};return new F(function(){return _vZ(_t5);});}else{var _wF=function(_wG){while(1){var _wH=E(_wG);if(!_wH._){return true;}else{var _wI=_wH.b,_wJ=E(_wH.a),_wK=E(_wJ.a);if(E(_wK.a)!=_ta){_wG=_wI;continue;}else{if(E(_wK.b)!=_uA){_wG=_wI;continue;}else{var _wL=u_iswupper(E(_wJ.b));if(!E(_wL)){return false;}else{_wG=_wI;continue;}}}}}};if(!B((function(_wM,_wN){var _wO=E(_wM),_wP=E(_wO.a);if(E(_wP.a)!=_ta){return new F(function(){return _wF(_wN);});}else{if(E(_wP.b)!=_uA){return new F(function(){return _wF(_wN);});}else{var _wQ=u_iswupper(E(_wO.b));if(!E(_wQ)){return false;}else{return new F(function(){return _wF(_wN);});}}}})(_dC,_dD))){var _wR=function(_wS){while(1){var _wT=B((function(_wU){var _wV=E(_wU);if(!_wV._){return E(_t3);}else{var _wW=_wV.b,_wX=E(_wV.a),_wY=_t8+E(_wX.a)|0;if(_wY<1){_wS=_wW;return __continue;}else{if(_wY>8){_wS=_wW;return __continue;}else{var _wZ=_uz+E(_wX.b)|0;if(_wZ<1){_wS=_wW;return __continue;}else{if(_wZ>8){_wS=_wW;return __continue;}else{var _x0=B(_4i(_t8,_uz,_wY,_wZ));if(!_x0._){return E(_cr);}else{var _x1=E(_x0.b);if(!_x1._){return E(_8I);}else{if(!B(_sE(B(_8D(_x1.a,_x1.b))))){_wS=_wW;return __continue;}else{var _x2=function(_x3){while(1){var _x4=E(_x3);if(!_x4._){return true;}else{var _x5=_x4.b,_x6=E(_x4.a),_x7=E(_x6.a);if(E(_x7.a)!=_wY){_x3=_x5;continue;}else{if(E(_x7.b)!=_wZ){_x3=_x5;continue;}else{var _x8=u_iswupper(E(_x6.b));if(!E(_x8)){return false;}else{_x3=_x5;continue;}}}}}};if(!B((function(_x9,_xa){var _xb=E(_x9),_xc=E(_xb.a);if(E(_xc.a)!=_wY){return new F(function(){return _x2(_xa);});}else{if(E(_xc.b)!=_wZ){return new F(function(){return _x2(_xa);});}else{var _xd=u_iswupper(E(_xb.b));if(!E(_xd)){return false;}else{return new F(function(){return _x2(_xa);});}}}})(_dC,_dD))){_wS=_wW;return __continue;}else{var _xe=new T(function(){var _xf=function(_xg){while(1){var _xh=E(_xg);if(!_xh._){return false;}else{var _xi=_xh.b,_xj=E(E(_xh.a).a);if(E(_xj.a)!=_wY){_xg=_xi;continue;}else{if(E(_xj.b)!=_wZ){_xg=_xi;continue;}else{return true;}}}}};if(!B((function(_xk,_xl){var _xm=E(E(_xk).a);if(E(_xm.a)!=_wY){return new F(function(){return _xf(_xl);});}else{if(E(_xm.b)!=_wZ){return new F(function(){return _xf(_xl);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_xn=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_wY)==8){if(E(_wZ)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_wY)==1){if(E(_wZ)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_xo=new T(function(){var _xp=function(_xq){var _xr=E(_xq),_xs=E(_xr.a),_xt=_xs.b,_xu=E(_xs.a),_xv=function(_xw){return (_xu!=_t8)?true:(E(_xt)!=_uz)?true:(E(_xr.b)==98)?false:true;};if(_xu!=_wY){return new F(function(){return _xv(_);});}else{if(E(_xt)!=_wZ){return new F(function(){return _xv(_);});}else{return false;}}};return B(_5R(_xp,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_wY,_wZ),_bP),_xo),b:_5L,c:_xn,d:_ds,e:_xe,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_wR(_wW));}));}}}}}}}}}})(_wS));if(_wT!=__continue){return _wT;}}};return new F(function(){return _wR(_t5);});}else{var _xx=new T(function(){var _xy=function(_xz){while(1){var _xA=B((function(_xB){var _xC=E(_xB);if(!_xC._){return E(_t3);}else{var _xD=_xC.b,_xE=E(_xC.a),_xF=_t8+E(_xE.a)|0;if(_xF<1){_xz=_xD;return __continue;}else{if(_xF>8){_xz=_xD;return __continue;}else{var _xG=_uz+E(_xE.b)|0;if(_xG<1){_xz=_xD;return __continue;}else{if(_xG>8){_xz=_xD;return __continue;}else{var _xH=B(_4i(_t8,_uz,_xF,_xG));if(!_xH._){return E(_cr);}else{var _xI=E(_xH.b);if(!_xI._){return E(_8I);}else{if(!B(_sE(B(_8D(_xI.a,_xI.b))))){_xz=_xD;return __continue;}else{var _xJ=function(_xK){while(1){var _xL=E(_xK);if(!_xL._){return true;}else{var _xM=_xL.b,_xN=E(_xL.a),_xO=E(_xN.a);if(E(_xO.a)!=_xF){_xK=_xM;continue;}else{if(E(_xO.b)!=_xG){_xK=_xM;continue;}else{var _xP=u_iswupper(E(_xN.b));if(!E(_xP)){return false;}else{_xK=_xM;continue;}}}}}};if(!B((function(_xQ,_xR){var _xS=E(_xQ),_xT=E(_xS.a);if(E(_xT.a)!=_xF){return new F(function(){return _xJ(_xR);});}else{if(E(_xT.b)!=_xG){return new F(function(){return _xJ(_xR);});}else{var _xU=u_iswupper(E(_xS.b));if(!E(_xU)){return false;}else{return new F(function(){return _xJ(_xR);});}}}})(_dC,_dD))){_xz=_xD;return __continue;}else{var _xV=new T(function(){var _xW=function(_xX){while(1){var _xY=E(_xX);if(!_xY._){return false;}else{var _xZ=_xY.b,_y0=E(E(_xY.a).a);if(E(_y0.a)!=_xF){_xX=_xZ;continue;}else{if(E(_y0.b)!=_xG){_xX=_xZ;continue;}else{return true;}}}}};if(!B((function(_y1,_y2){var _y3=E(E(_y1).a);if(E(_y3.a)!=_xF){return new F(function(){return _xW(_y2);});}else{if(E(_y3.b)!=_xG){return new F(function(){return _xW(_y2);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_y4=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_xF)==8){if(E(_xG)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_xF)==1){if(E(_xG)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_y5=new T(function(){var _y6=function(_y7){var _y8=E(_y7),_y9=E(_y8.a),_ya=_y9.b,_yb=E(_y9.a),_yc=function(_yd){return (_yb!=_t8)?true:(E(_ya)!=_uz)?true:(E(_y8.b)==98)?false:true;};if(_yb!=_xF){return new F(function(){return _yc(_);});}else{if(E(_ya)!=_xG){return new F(function(){return _yc(_);});}else{return false;}}};return B(_5R(_y6,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_xF,_xG),_bP),_y5),b:_5L,c:_y4,d:_ds,e:_xV,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_xy(_xD));}));}}}}}}}}}})(_xz));if(_xA!=__continue){return _xA;}}};return B(_xy(_t5));}),_ye=new T(function(){var _yf=function(_yg){while(1){var _yh=E(_yg);if(!_yh._){return false;}else{var _yi=_yh.b,_yj=E(E(_yh.a).a);if(E(_yj.a)!=_ta){_yg=_yi;continue;}else{if(E(_yj.b)!=_uA){_yg=_yi;continue;}else{return true;}}}}};if(!B((function(_yk,_yl){var _ym=E(E(_yk).a);if(E(_ym.a)!=_ta){return new F(function(){return _yf(_yl);});}else{if(E(_ym.b)!=_uA){return new F(function(){return _yf(_yl);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_yn=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_ta)==8){if(E(_uA)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_ta)==1){if(E(_uA)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_yo=new T(function(){var _yp=function(_yq){var _yr=E(_yq),_ys=E(_yr.a),_yt=_ys.b,_yu=E(_ys.a),_yv=function(_yw){return (_yu!=_t8)?true:(E(_yt)!=_uz)?true:(E(_yr.b)==98)?false:true;};if(_yu!=_ta){return new F(function(){return _yv(_);});}else{if(E(_yt)!=_uA){return new F(function(){return _yv(_);});}else{return false;}}};return B(_5R(_yp,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_ta,_uA),_bP),_yo),b:_5L,c:_yn,d:_ds,e:_ye,f:_8S,g:_8L,h:_8L,i:_5K},_xx);}}}}}}}}}}else{return E(_t3);}}},_yx=function(_yy,_yz){var _yA=E(_yy),_yB=new T(function(){return B(_sZ(_yz));});if(E(_yA.b)==98){var _yC=E(_bN);if(!_yC._){return E(_yB);}else{var _yD=_yC.b,_yE=E(_yA.a),_yF=_yE.b,_yG=E(_yE.a),_yH=E(_yC.a),_yI=_yG+E(_yH.a)|0;if(_yI<1){var _yJ=function(_yK){while(1){var _yL=B((function(_yM){var _yN=E(_yM);if(!_yN._){return E(_yB);}else{var _yO=_yN.b,_yP=E(_yN.a),_yQ=_yG+E(_yP.a)|0;if(_yQ<1){_yK=_yO;return __continue;}else{if(_yQ>8){_yK=_yO;return __continue;}else{var _yR=E(_yF),_yS=_yR+E(_yP.b)|0;if(_yS<1){_yK=_yO;return __continue;}else{if(_yS>8){_yK=_yO;return __continue;}else{var _yT=B(_4i(_yG,_yR,_yQ,_yS));if(!_yT._){return E(_cr);}else{var _yU=E(_yT.b);if(!_yU._){return E(_8I);}else{if(!B(_sE(B(_8D(_yU.a,_yU.b))))){_yK=_yO;return __continue;}else{var _yV=function(_yW){while(1){var _yX=E(_yW);if(!_yX._){return true;}else{var _yY=_yX.b,_yZ=E(_yX.a),_z0=E(_yZ.a);if(E(_z0.a)!=_yQ){_yW=_yY;continue;}else{if(E(_z0.b)!=_yS){_yW=_yY;continue;}else{var _z1=u_iswupper(E(_yZ.b));if(!E(_z1)){return false;}else{_yW=_yY;continue;}}}}}};if(!B((function(_z2,_z3){var _z4=E(_z2),_z5=E(_z4.a);if(E(_z5.a)!=_yQ){return new F(function(){return _yV(_z3);});}else{if(E(_z5.b)!=_yS){return new F(function(){return _yV(_z3);});}else{var _z6=u_iswupper(E(_z4.b));if(!E(_z6)){return false;}else{return new F(function(){return _yV(_z3);});}}}})(_dC,_dD))){_yK=_yO;return __continue;}else{var _z7=new T(function(){var _z8=function(_z9){while(1){var _za=E(_z9);if(!_za._){return false;}else{var _zb=_za.b,_zc=E(E(_za.a).a);if(E(_zc.a)!=_yQ){_z9=_zb;continue;}else{if(E(_zc.b)!=_yS){_z9=_zb;continue;}else{return true;}}}}};if(!B((function(_zd,_ze){var _zf=E(E(_zd).a);if(E(_zf.a)!=_yQ){return new F(function(){return _z8(_ze);});}else{if(E(_zf.b)!=_yS){return new F(function(){return _z8(_ze);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_zg=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_yQ)==8){if(E(_yS)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_yQ)==1){if(E(_yS)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_zh=new T(function(){var _zi=function(_zj){var _zk=E(_zj),_zl=E(_zk.a),_zm=_zl.b,_zn=E(_zl.a),_zo=function(_zp){return (_zn!=_yG)?true:(E(_zm)!=_yR)?true:(E(_zk.b)==98)?false:true;};if(_zn!=_yQ){return new F(function(){return _zo(_);});}else{if(E(_zm)!=_yS){return new F(function(){return _zo(_);});}else{return false;}}};return B(_5R(_zi,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_yQ,_yS),_bP),_zh),b:_5L,c:_zg,d:_ds,e:_z7,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_yJ(_yO));}));}}}}}}}}}})(_yK));if(_yL!=__continue){return _yL;}}};return new F(function(){return _yJ(_yD);});}else{if(_yI>8){var _zq=function(_zr){while(1){var _zs=B((function(_zt){var _zu=E(_zt);if(!_zu._){return E(_yB);}else{var _zv=_zu.b,_zw=E(_zu.a),_zx=_yG+E(_zw.a)|0;if(_zx<1){_zr=_zv;return __continue;}else{if(_zx>8){_zr=_zv;return __continue;}else{var _zy=E(_yF),_zz=_zy+E(_zw.b)|0;if(_zz<1){_zr=_zv;return __continue;}else{if(_zz>8){_zr=_zv;return __continue;}else{var _zA=B(_4i(_yG,_zy,_zx,_zz));if(!_zA._){return E(_cr);}else{var _zB=E(_zA.b);if(!_zB._){return E(_8I);}else{if(!B(_sE(B(_8D(_zB.a,_zB.b))))){_zr=_zv;return __continue;}else{var _zC=function(_zD){while(1){var _zE=E(_zD);if(!_zE._){return true;}else{var _zF=_zE.b,_zG=E(_zE.a),_zH=E(_zG.a);if(E(_zH.a)!=_zx){_zD=_zF;continue;}else{if(E(_zH.b)!=_zz){_zD=_zF;continue;}else{var _zI=u_iswupper(E(_zG.b));if(!E(_zI)){return false;}else{_zD=_zF;continue;}}}}}};if(!B((function(_zJ,_zK){var _zL=E(_zJ),_zM=E(_zL.a);if(E(_zM.a)!=_zx){return new F(function(){return _zC(_zK);});}else{if(E(_zM.b)!=_zz){return new F(function(){return _zC(_zK);});}else{var _zN=u_iswupper(E(_zL.b));if(!E(_zN)){return false;}else{return new F(function(){return _zC(_zK);});}}}})(_dC,_dD))){_zr=_zv;return __continue;}else{var _zO=new T(function(){var _zP=function(_zQ){while(1){var _zR=E(_zQ);if(!_zR._){return false;}else{var _zS=_zR.b,_zT=E(E(_zR.a).a);if(E(_zT.a)!=_zx){_zQ=_zS;continue;}else{if(E(_zT.b)!=_zz){_zQ=_zS;continue;}else{return true;}}}}};if(!B((function(_zU,_zV){var _zW=E(E(_zU).a);if(E(_zW.a)!=_zx){return new F(function(){return _zP(_zV);});}else{if(E(_zW.b)!=_zz){return new F(function(){return _zP(_zV);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_zX=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_zx)==8){if(E(_zz)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_zx)==1){if(E(_zz)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_zY=new T(function(){var _zZ=function(_A0){var _A1=E(_A0),_A2=E(_A1.a),_A3=_A2.b,_A4=E(_A2.a),_A5=function(_A6){return (_A4!=_yG)?true:(E(_A3)!=_zy)?true:(E(_A1.b)==98)?false:true;};if(_A4!=_zx){return new F(function(){return _A5(_);});}else{if(E(_A3)!=_zz){return new F(function(){return _A5(_);});}else{return false;}}};return B(_5R(_zZ,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_zx,_zz),_bP),_zY),b:_5L,c:_zX,d:_ds,e:_zO,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_zq(_zv));}));}}}}}}}}}})(_zr));if(_zs!=__continue){return _zs;}}};return new F(function(){return _zq(_yD);});}else{var _A7=E(_yF),_A8=_A7+E(_yH.b)|0;if(_A8<1){var _A9=function(_Aa){while(1){var _Ab=B((function(_Ac){var _Ad=E(_Ac);if(!_Ad._){return E(_yB);}else{var _Ae=_Ad.b,_Af=E(_Ad.a),_Ag=_yG+E(_Af.a)|0;if(_Ag<1){_Aa=_Ae;return __continue;}else{if(_Ag>8){_Aa=_Ae;return __continue;}else{var _Ah=_A7+E(_Af.b)|0;if(_Ah<1){_Aa=_Ae;return __continue;}else{if(_Ah>8){_Aa=_Ae;return __continue;}else{var _Ai=B(_4i(_yG,_A7,_Ag,_Ah));if(!_Ai._){return E(_cr);}else{var _Aj=E(_Ai.b);if(!_Aj._){return E(_8I);}else{if(!B(_sE(B(_8D(_Aj.a,_Aj.b))))){_Aa=_Ae;return __continue;}else{var _Ak=function(_Al){while(1){var _Am=E(_Al);if(!_Am._){return true;}else{var _An=_Am.b,_Ao=E(_Am.a),_Ap=E(_Ao.a);if(E(_Ap.a)!=_Ag){_Al=_An;continue;}else{if(E(_Ap.b)!=_Ah){_Al=_An;continue;}else{var _Aq=u_iswupper(E(_Ao.b));if(!E(_Aq)){return false;}else{_Al=_An;continue;}}}}}};if(!B((function(_Ar,_As){var _At=E(_Ar),_Au=E(_At.a);if(E(_Au.a)!=_Ag){return new F(function(){return _Ak(_As);});}else{if(E(_Au.b)!=_Ah){return new F(function(){return _Ak(_As);});}else{var _Av=u_iswupper(E(_At.b));if(!E(_Av)){return false;}else{return new F(function(){return _Ak(_As);});}}}})(_dC,_dD))){_Aa=_Ae;return __continue;}else{var _Aw=new T(function(){var _Ax=function(_Ay){while(1){var _Az=E(_Ay);if(!_Az._){return false;}else{var _AA=_Az.b,_AB=E(E(_Az.a).a);if(E(_AB.a)!=_Ag){_Ay=_AA;continue;}else{if(E(_AB.b)!=_Ah){_Ay=_AA;continue;}else{return true;}}}}};if(!B((function(_AC,_AD){var _AE=E(E(_AC).a);if(E(_AE.a)!=_Ag){return new F(function(){return _Ax(_AD);});}else{if(E(_AE.b)!=_Ah){return new F(function(){return _Ax(_AD);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_AF=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_Ag)==8){if(E(_Ah)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_Ag)==1){if(E(_Ah)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_AG=new T(function(){var _AH=function(_AI){var _AJ=E(_AI),_AK=E(_AJ.a),_AL=_AK.b,_AM=E(_AK.a),_AN=function(_AO){return (_AM!=_yG)?true:(E(_AL)!=_A7)?true:(E(_AJ.b)==98)?false:true;};if(_AM!=_Ag){return new F(function(){return _AN(_);});}else{if(E(_AL)!=_Ah){return new F(function(){return _AN(_);});}else{return false;}}};return B(_5R(_AH,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_Ag,_Ah),_bP),_AG),b:_5L,c:_AF,d:_ds,e:_Aw,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_A9(_Ae));}));}}}}}}}}}})(_Aa));if(_Ab!=__continue){return _Ab;}}};return new F(function(){return _A9(_yD);});}else{if(_A8>8){var _AP=function(_AQ){while(1){var _AR=B((function(_AS){var _AT=E(_AS);if(!_AT._){return E(_yB);}else{var _AU=_AT.b,_AV=E(_AT.a),_AW=_yG+E(_AV.a)|0;if(_AW<1){_AQ=_AU;return __continue;}else{if(_AW>8){_AQ=_AU;return __continue;}else{var _AX=_A7+E(_AV.b)|0;if(_AX<1){_AQ=_AU;return __continue;}else{if(_AX>8){_AQ=_AU;return __continue;}else{var _AY=B(_4i(_yG,_A7,_AW,_AX));if(!_AY._){return E(_cr);}else{var _AZ=E(_AY.b);if(!_AZ._){return E(_8I);}else{if(!B(_sE(B(_8D(_AZ.a,_AZ.b))))){_AQ=_AU;return __continue;}else{var _B0=function(_B1){while(1){var _B2=E(_B1);if(!_B2._){return true;}else{var _B3=_B2.b,_B4=E(_B2.a),_B5=E(_B4.a);if(E(_B5.a)!=_AW){_B1=_B3;continue;}else{if(E(_B5.b)!=_AX){_B1=_B3;continue;}else{var _B6=u_iswupper(E(_B4.b));if(!E(_B6)){return false;}else{_B1=_B3;continue;}}}}}};if(!B((function(_B7,_B8){var _B9=E(_B7),_Ba=E(_B9.a);if(E(_Ba.a)!=_AW){return new F(function(){return _B0(_B8);});}else{if(E(_Ba.b)!=_AX){return new F(function(){return _B0(_B8);});}else{var _Bb=u_iswupper(E(_B9.b));if(!E(_Bb)){return false;}else{return new F(function(){return _B0(_B8);});}}}})(_dC,_dD))){_AQ=_AU;return __continue;}else{var _Bc=new T(function(){var _Bd=function(_Be){while(1){var _Bf=E(_Be);if(!_Bf._){return false;}else{var _Bg=_Bf.b,_Bh=E(E(_Bf.a).a);if(E(_Bh.a)!=_AW){_Be=_Bg;continue;}else{if(E(_Bh.b)!=_AX){_Be=_Bg;continue;}else{return true;}}}}};if(!B((function(_Bi,_Bj){var _Bk=E(E(_Bi).a);if(E(_Bk.a)!=_AW){return new F(function(){return _Bd(_Bj);});}else{if(E(_Bk.b)!=_AX){return new F(function(){return _Bd(_Bj);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_Bl=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_AW)==8){if(E(_AX)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_AW)==1){if(E(_AX)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_Bm=new T(function(){var _Bn=function(_Bo){var _Bp=E(_Bo),_Bq=E(_Bp.a),_Br=_Bq.b,_Bs=E(_Bq.a),_Bt=function(_Bu){return (_Bs!=_yG)?true:(E(_Br)!=_A7)?true:(E(_Bp.b)==98)?false:true;};if(_Bs!=_AW){return new F(function(){return _Bt(_);});}else{if(E(_Br)!=_AX){return new F(function(){return _Bt(_);});}else{return false;}}};return B(_5R(_Bn,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_AW,_AX),_bP),_Bm),b:_5L,c:_Bl,d:_ds,e:_Bc,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_AP(_AU));}));}}}}}}}}}})(_AQ));if(_AR!=__continue){return _AR;}}};return new F(function(){return _AP(_yD);});}else{var _Bv=B(_4i(_yG,_A7,_yI,_A8));if(!_Bv._){return E(_cr);}else{var _Bw=E(_Bv.b);if(!_Bw._){return E(_8I);}else{if(!B(_sE(B(_8D(_Bw.a,_Bw.b))))){var _Bx=function(_By){while(1){var _Bz=B((function(_BA){var _BB=E(_BA);if(!_BB._){return E(_yB);}else{var _BC=_BB.b,_BD=E(_BB.a),_BE=_yG+E(_BD.a)|0;if(_BE<1){_By=_BC;return __continue;}else{if(_BE>8){_By=_BC;return __continue;}else{var _BF=_A7+E(_BD.b)|0;if(_BF<1){_By=_BC;return __continue;}else{if(_BF>8){_By=_BC;return __continue;}else{var _BG=B(_4i(_yG,_A7,_BE,_BF));if(!_BG._){return E(_cr);}else{var _BH=E(_BG.b);if(!_BH._){return E(_8I);}else{if(!B(_sE(B(_8D(_BH.a,_BH.b))))){_By=_BC;return __continue;}else{var _BI=function(_BJ){while(1){var _BK=E(_BJ);if(!_BK._){return true;}else{var _BL=_BK.b,_BM=E(_BK.a),_BN=E(_BM.a);if(E(_BN.a)!=_BE){_BJ=_BL;continue;}else{if(E(_BN.b)!=_BF){_BJ=_BL;continue;}else{var _BO=u_iswupper(E(_BM.b));if(!E(_BO)){return false;}else{_BJ=_BL;continue;}}}}}};if(!B((function(_BP,_BQ){var _BR=E(_BP),_BS=E(_BR.a);if(E(_BS.a)!=_BE){return new F(function(){return _BI(_BQ);});}else{if(E(_BS.b)!=_BF){return new F(function(){return _BI(_BQ);});}else{var _BT=u_iswupper(E(_BR.b));if(!E(_BT)){return false;}else{return new F(function(){return _BI(_BQ);});}}}})(_dC,_dD))){_By=_BC;return __continue;}else{var _BU=new T(function(){var _BV=function(_BW){while(1){var _BX=E(_BW);if(!_BX._){return false;}else{var _BY=_BX.b,_BZ=E(E(_BX.a).a);if(E(_BZ.a)!=_BE){_BW=_BY;continue;}else{if(E(_BZ.b)!=_BF){_BW=_BY;continue;}else{return true;}}}}};if(!B((function(_C0,_C1){var _C2=E(E(_C0).a);if(E(_C2.a)!=_BE){return new F(function(){return _BV(_C1);});}else{if(E(_C2.b)!=_BF){return new F(function(){return _BV(_C1);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_C3=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_BE)==8){if(E(_BF)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_BE)==1){if(E(_BF)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_C4=new T(function(){var _C5=function(_C6){var _C7=E(_C6),_C8=E(_C7.a),_C9=_C8.b,_Ca=E(_C8.a),_Cb=function(_Cc){return (_Ca!=_yG)?true:(E(_C9)!=_A7)?true:(E(_C7.b)==98)?false:true;};if(_Ca!=_BE){return new F(function(){return _Cb(_);});}else{if(E(_C9)!=_BF){return new F(function(){return _Cb(_);});}else{return false;}}};return B(_5R(_C5,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_BE,_BF),_bP),_C4),b:_5L,c:_C3,d:_ds,e:_BU,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_Bx(_BC));}));}}}}}}}}}})(_By));if(_Bz!=__continue){return _Bz;}}};return new F(function(){return _Bx(_yD);});}else{var _Cd=function(_Ce){while(1){var _Cf=E(_Ce);if(!_Cf._){return true;}else{var _Cg=_Cf.b,_Ch=E(_Cf.a),_Ci=E(_Ch.a);if(E(_Ci.a)!=_yI){_Ce=_Cg;continue;}else{if(E(_Ci.b)!=_A8){_Ce=_Cg;continue;}else{var _Cj=u_iswupper(E(_Ch.b));if(!E(_Cj)){return false;}else{_Ce=_Cg;continue;}}}}}};if(!B((function(_Ck,_Cl){var _Cm=E(_Ck),_Cn=E(_Cm.a);if(E(_Cn.a)!=_yI){return new F(function(){return _Cd(_Cl);});}else{if(E(_Cn.b)!=_A8){return new F(function(){return _Cd(_Cl);});}else{var _Co=u_iswupper(E(_Cm.b));if(!E(_Co)){return false;}else{return new F(function(){return _Cd(_Cl);});}}}})(_dC,_dD))){var _Cp=function(_Cq){while(1){var _Cr=B((function(_Cs){var _Ct=E(_Cs);if(!_Ct._){return E(_yB);}else{var _Cu=_Ct.b,_Cv=E(_Ct.a),_Cw=_yG+E(_Cv.a)|0;if(_Cw<1){_Cq=_Cu;return __continue;}else{if(_Cw>8){_Cq=_Cu;return __continue;}else{var _Cx=_A7+E(_Cv.b)|0;if(_Cx<1){_Cq=_Cu;return __continue;}else{if(_Cx>8){_Cq=_Cu;return __continue;}else{var _Cy=B(_4i(_yG,_A7,_Cw,_Cx));if(!_Cy._){return E(_cr);}else{var _Cz=E(_Cy.b);if(!_Cz._){return E(_8I);}else{if(!B(_sE(B(_8D(_Cz.a,_Cz.b))))){_Cq=_Cu;return __continue;}else{var _CA=function(_CB){while(1){var _CC=E(_CB);if(!_CC._){return true;}else{var _CD=_CC.b,_CE=E(_CC.a),_CF=E(_CE.a);if(E(_CF.a)!=_Cw){_CB=_CD;continue;}else{if(E(_CF.b)!=_Cx){_CB=_CD;continue;}else{var _CG=u_iswupper(E(_CE.b));if(!E(_CG)){return false;}else{_CB=_CD;continue;}}}}}};if(!B((function(_CH,_CI){var _CJ=E(_CH),_CK=E(_CJ.a);if(E(_CK.a)!=_Cw){return new F(function(){return _CA(_CI);});}else{if(E(_CK.b)!=_Cx){return new F(function(){return _CA(_CI);});}else{var _CL=u_iswupper(E(_CJ.b));if(!E(_CL)){return false;}else{return new F(function(){return _CA(_CI);});}}}})(_dC,_dD))){_Cq=_Cu;return __continue;}else{var _CM=new T(function(){var _CN=function(_CO){while(1){var _CP=E(_CO);if(!_CP._){return false;}else{var _CQ=_CP.b,_CR=E(E(_CP.a).a);if(E(_CR.a)!=_Cw){_CO=_CQ;continue;}else{if(E(_CR.b)!=_Cx){_CO=_CQ;continue;}else{return true;}}}}};if(!B((function(_CS,_CT){var _CU=E(E(_CS).a);if(E(_CU.a)!=_Cw){return new F(function(){return _CN(_CT);});}else{if(E(_CU.b)!=_Cx){return new F(function(){return _CN(_CT);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_CV=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_Cw)==8){if(E(_Cx)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_Cw)==1){if(E(_Cx)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_CW=new T(function(){var _CX=function(_CY){var _CZ=E(_CY),_D0=E(_CZ.a),_D1=_D0.b,_D2=E(_D0.a),_D3=function(_D4){return (_D2!=_yG)?true:(E(_D1)!=_A7)?true:(E(_CZ.b)==98)?false:true;};if(_D2!=_Cw){return new F(function(){return _D3(_);});}else{if(E(_D1)!=_Cx){return new F(function(){return _D3(_);});}else{return false;}}};return B(_5R(_CX,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_Cw,_Cx),_bP),_CW),b:_5L,c:_CV,d:_ds,e:_CM,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_Cp(_Cu));}));}}}}}}}}}})(_Cq));if(_Cr!=__continue){return _Cr;}}};return new F(function(){return _Cp(_yD);});}else{var _D5=new T(function(){var _D6=function(_D7){while(1){var _D8=B((function(_D9){var _Da=E(_D9);if(!_Da._){return E(_yB);}else{var _Db=_Da.b,_Dc=E(_Da.a),_Dd=_yG+E(_Dc.a)|0;if(_Dd<1){_D7=_Db;return __continue;}else{if(_Dd>8){_D7=_Db;return __continue;}else{var _De=_A7+E(_Dc.b)|0;if(_De<1){_D7=_Db;return __continue;}else{if(_De>8){_D7=_Db;return __continue;}else{var _Df=B(_4i(_yG,_A7,_Dd,_De));if(!_Df._){return E(_cr);}else{var _Dg=E(_Df.b);if(!_Dg._){return E(_8I);}else{if(!B(_sE(B(_8D(_Dg.a,_Dg.b))))){_D7=_Db;return __continue;}else{var _Dh=function(_Di){while(1){var _Dj=E(_Di);if(!_Dj._){return true;}else{var _Dk=_Dj.b,_Dl=E(_Dj.a),_Dm=E(_Dl.a);if(E(_Dm.a)!=_Dd){_Di=_Dk;continue;}else{if(E(_Dm.b)!=_De){_Di=_Dk;continue;}else{var _Dn=u_iswupper(E(_Dl.b));if(!E(_Dn)){return false;}else{_Di=_Dk;continue;}}}}}};if(!B((function(_Do,_Dp){var _Dq=E(_Do),_Dr=E(_Dq.a);if(E(_Dr.a)!=_Dd){return new F(function(){return _Dh(_Dp);});}else{if(E(_Dr.b)!=_De){return new F(function(){return _Dh(_Dp);});}else{var _Ds=u_iswupper(E(_Dq.b));if(!E(_Ds)){return false;}else{return new F(function(){return _Dh(_Dp);});}}}})(_dC,_dD))){_D7=_Db;return __continue;}else{var _Dt=new T(function(){var _Du=function(_Dv){while(1){var _Dw=E(_Dv);if(!_Dw._){return false;}else{var _Dx=_Dw.b,_Dy=E(E(_Dw.a).a);if(E(_Dy.a)!=_Dd){_Dv=_Dx;continue;}else{if(E(_Dy.b)!=_De){_Dv=_Dx;continue;}else{return true;}}}}};if(!B((function(_Dz,_DA){var _DB=E(E(_Dz).a);if(E(_DB.a)!=_Dd){return new F(function(){return _Du(_DA);});}else{if(E(_DB.b)!=_De){return new F(function(){return _Du(_DA);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_DC=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_Dd)==8){if(E(_De)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_Dd)==1){if(E(_De)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_DD=new T(function(){var _DE=function(_DF){var _DG=E(_DF),_DH=E(_DG.a),_DI=_DH.b,_DJ=E(_DH.a),_DK=function(_DL){return (_DJ!=_yG)?true:(E(_DI)!=_A7)?true:(E(_DG.b)==98)?false:true;};if(_DJ!=_Dd){return new F(function(){return _DK(_);});}else{if(E(_DI)!=_De){return new F(function(){return _DK(_);});}else{return false;}}};return B(_5R(_DE,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_Dd,_De),_bP),_DD),b:_5L,c:_DC,d:_ds,e:_Dt,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_D6(_Db));}));}}}}}}}}}})(_D7));if(_D8!=__continue){return _D8;}}};return B(_D6(_yD));}),_DM=new T(function(){var _DN=function(_DO){while(1){var _DP=E(_DO);if(!_DP._){return false;}else{var _DQ=_DP.b,_DR=E(E(_DP.a).a);if(E(_DR.a)!=_yI){_DO=_DQ;continue;}else{if(E(_DR.b)!=_A8){_DO=_DQ;continue;}else{return true;}}}}};if(!B((function(_DS,_DT){var _DU=E(E(_DS).a);if(E(_DU.a)!=_yI){return new F(function(){return _DN(_DT);});}else{if(E(_DU.b)!=_A8){return new F(function(){return _DN(_DT);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_DV=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_yI)==8){if(E(_A8)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_yI)==1){if(E(_A8)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_DW=new T(function(){var _DX=function(_DY){var _DZ=E(_DY),_E0=E(_DZ.a),_E1=_E0.b,_E2=E(_E0.a),_E3=function(_E4){return (_E2!=_yG)?true:(E(_E1)!=_A7)?true:(E(_DZ.b)==98)?false:true;};if(_E2!=_yI){return new F(function(){return _E3(_);});}else{if(E(_E1)!=_A8){return new F(function(){return _E3(_);});}else{return false;}}};return B(_5R(_DX,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_yI,_A8),_bP),_DW),b:_5L,c:_DV,d:_ds,e:_DM,f:_8S,g:_8L,h:_8L,i:_5K},_D5);}}}}}}}}}}else{return E(_yB);}};return B(_yx(_dC,_dD));}),_E5=function(_E6){while(1){var _E7=B((function(_E8){var _E9=E(_E8);if(!_E9._){return true;}else{var _Ea=_E9.b,_Eb=E(E(_dC).a),_Ec=E(_E9.a),_Ed=_Ec.b,_Ee=E(_Ec.a);if(E(_Eb.a)!=_Ee){var _Ef=function(_Eg){while(1){var _Eh=E(_Eg);if(!_Eh._){return true;}else{var _Ei=_Eh.b,_Ej=E(E(_Eh.a).a);if(E(_Ej.a)!=_Ee){_Eg=_Ei;continue;}else{if(E(_Ej.b)!=E(_Ed)){_Eg=_Ei;continue;}else{return false;}}}}};if(!B(_Ef(_dD))){return false;}else{_E6=_Ea;return __continue;}}else{var _Ek=E(_Ed);if(E(_Eb.b)!=_Ek){var _El=function(_Em){while(1){var _En=E(_Em);if(!_En._){return true;}else{var _Eo=_En.b,_Ep=E(E(_En.a).a);if(E(_Ep.a)!=_Ee){_Em=_Eo;continue;}else{if(E(_Ep.b)!=_Ek){_Em=_Eo;continue;}else{return false;}}}}};if(!B(_El(_dD))){return false;}else{_E6=_Ea;return __continue;}}else{return false;}}}})(_E6));if(_E7!=__continue){return _E7;}}},_Eq=function(_Er){var _Es=E(_Er);if(!_Es._){return E(_eO);}else{var _Et=E(_Es.a),_Eu=_Et.a,_Ev=new T(function(){return B(_Eq(_Es.b));});if(E(_Et.b)==114){var _Ew=new T(function(){return B(_5B(2,new T(function(){var _Ex=E(_Eu);if(E(_Ex.a)==8){if(E(_Ex.b)==8){return true;}else{return E(_dy);}}else{return E(_dy);}}),B(_5B(3,new T(function(){var _Ey=E(_Eu);if(E(_Ey.a)==1){if(E(_Ey.b)==8){return true;}else{return E(_dx);}}else{return E(_dx);}}),_dr))));}),_Ez=E(_cg);if(!_Ez._){return E(_Ev);}else{var _EA=_Ez.b,_EB=E(_Eu),_EC=_EB.b,_ED=E(_EB.a),_EE=E(_Ez.a),_EF=_ED+E(_EE.a)|0;if(_EF<1){var _EG=function(_EH){while(1){var _EI=B((function(_EJ){var _EK=E(_EJ);if(!_EK._){return E(_Ev);}else{var _EL=_EK.b,_EM=E(_EK.a),_EN=_ED+E(_EM.a)|0;if(_EN<1){_EH=_EL;return __continue;}else{if(_EN>8){_EH=_EL;return __continue;}else{var _EO=E(_EC),_EP=_EO+E(_EM.b)|0;if(_EP<1){_EH=_EL;return __continue;}else{if(_EP>8){_EH=_EL;return __continue;}else{var _EQ=B(_4i(_ED,_EO,_EN,_EP));if(!_EQ._){return E(_cr);}else{var _ER=E(_EQ.b);if(!_ER._){return E(_8I);}else{if(!B(_E5(B(_8D(_ER.a,_ER.b))))){_EH=_EL;return __continue;}else{var _ES=function(_ET){while(1){var _EU=E(_ET);if(!_EU._){return true;}else{var _EV=_EU.b,_EW=E(_EU.a),_EX=E(_EW.a);if(E(_EX.a)!=_EN){_ET=_EV;continue;}else{if(E(_EX.b)!=_EP){_ET=_EV;continue;}else{var _EY=u_iswupper(E(_EW.b));if(!E(_EY)){return false;}else{_ET=_EV;continue;}}}}}};if(!B((function(_EZ,_F0){var _F1=E(_EZ),_F2=E(_F1.a);if(E(_F2.a)!=_EN){return new F(function(){return _ES(_F0);});}else{if(E(_F2.b)!=_EP){return new F(function(){return _ES(_F0);});}else{var _F3=u_iswupper(E(_F1.b));if(!E(_F3)){return false;}else{return new F(function(){return _ES(_F0);});}}}})(_dC,_dD))){_EH=_EL;return __continue;}else{var _F4=new T(function(){var _F5=function(_F6){while(1){var _F7=E(_F6);if(!_F7._){return false;}else{var _F8=_F7.b,_F9=E(E(_F7.a).a);if(E(_F9.a)!=_EN){_F6=_F8;continue;}else{if(E(_F9.b)!=_EP){_F6=_F8;continue;}else{return true;}}}}};if(!B((function(_Fa,_Fb){var _Fc=E(E(_Fa).a);if(E(_Fc.a)!=_EN){return new F(function(){return _F5(_Fb);});}else{if(E(_Fc.b)!=_EP){return new F(function(){return _F5(_Fb);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_Fd=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_EN)==8){if(E(_EP)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_EN)==1){if(E(_EP)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_Ew))));}),_Fe=new T(function(){var _Ff=function(_Fg){var _Fh=E(_Fg),_Fi=E(_Fh.a),_Fj=_Fi.b,_Fk=E(_Fi.a),_Fl=function(_Fm){return (_Fk!=_ED)?true:(E(_Fj)!=_EO)?true:(E(_Fh.b)==114)?false:true;};if(_Fk!=_EN){return new F(function(){return _Fl(_);});}else{if(E(_Fj)!=_EP){return new F(function(){return _Fl(_);});}else{return false;}}};return B(_5R(_Ff,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_EN,_EP),_95),_Fe),b:_5L,c:_Fd,d:_ds,e:_F4,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_EG(_EL));}));}}}}}}}}}})(_EH));if(_EI!=__continue){return _EI;}}};return new F(function(){return _EG(_EA);});}else{if(_EF>8){var _Fn=function(_Fo){while(1){var _Fp=B((function(_Fq){var _Fr=E(_Fq);if(!_Fr._){return E(_Ev);}else{var _Fs=_Fr.b,_Ft=E(_Fr.a),_Fu=_ED+E(_Ft.a)|0;if(_Fu<1){_Fo=_Fs;return __continue;}else{if(_Fu>8){_Fo=_Fs;return __continue;}else{var _Fv=E(_EC),_Fw=_Fv+E(_Ft.b)|0;if(_Fw<1){_Fo=_Fs;return __continue;}else{if(_Fw>8){_Fo=_Fs;return __continue;}else{var _Fx=B(_4i(_ED,_Fv,_Fu,_Fw));if(!_Fx._){return E(_cr);}else{var _Fy=E(_Fx.b);if(!_Fy._){return E(_8I);}else{if(!B(_E5(B(_8D(_Fy.a,_Fy.b))))){_Fo=_Fs;return __continue;}else{var _Fz=function(_FA){while(1){var _FB=E(_FA);if(!_FB._){return true;}else{var _FC=_FB.b,_FD=E(_FB.a),_FE=E(_FD.a);if(E(_FE.a)!=_Fu){_FA=_FC;continue;}else{if(E(_FE.b)!=_Fw){_FA=_FC;continue;}else{var _FF=u_iswupper(E(_FD.b));if(!E(_FF)){return false;}else{_FA=_FC;continue;}}}}}};if(!B((function(_FG,_FH){var _FI=E(_FG),_FJ=E(_FI.a);if(E(_FJ.a)!=_Fu){return new F(function(){return _Fz(_FH);});}else{if(E(_FJ.b)!=_Fw){return new F(function(){return _Fz(_FH);});}else{var _FK=u_iswupper(E(_FI.b));if(!E(_FK)){return false;}else{return new F(function(){return _Fz(_FH);});}}}})(_dC,_dD))){_Fo=_Fs;return __continue;}else{var _FL=new T(function(){var _FM=function(_FN){while(1){var _FO=E(_FN);if(!_FO._){return false;}else{var _FP=_FO.b,_FQ=E(E(_FO.a).a);if(E(_FQ.a)!=_Fu){_FN=_FP;continue;}else{if(E(_FQ.b)!=_Fw){_FN=_FP;continue;}else{return true;}}}}};if(!B((function(_FR,_FS){var _FT=E(E(_FR).a);if(E(_FT.a)!=_Fu){return new F(function(){return _FM(_FS);});}else{if(E(_FT.b)!=_Fw){return new F(function(){return _FM(_FS);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_FU=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_Fu)==8){if(E(_Fw)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_Fu)==1){if(E(_Fw)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_Ew))));}),_FV=new T(function(){var _FW=function(_FX){var _FY=E(_FX),_FZ=E(_FY.a),_G0=_FZ.b,_G1=E(_FZ.a),_G2=function(_G3){return (_G1!=_ED)?true:(E(_G0)!=_Fv)?true:(E(_FY.b)==114)?false:true;};if(_G1!=_Fu){return new F(function(){return _G2(_);});}else{if(E(_G0)!=_Fw){return new F(function(){return _G2(_);});}else{return false;}}};return B(_5R(_FW,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_Fu,_Fw),_95),_FV),b:_5L,c:_FU,d:_ds,e:_FL,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_Fn(_Fs));}));}}}}}}}}}})(_Fo));if(_Fp!=__continue){return _Fp;}}};return new F(function(){return _Fn(_EA);});}else{var _G4=E(_EC),_G5=_G4+E(_EE.b)|0;if(_G5<1){var _G6=function(_G7){while(1){var _G8=B((function(_G9){var _Ga=E(_G9);if(!_Ga._){return E(_Ev);}else{var _Gb=_Ga.b,_Gc=E(_Ga.a),_Gd=_ED+E(_Gc.a)|0;if(_Gd<1){_G7=_Gb;return __continue;}else{if(_Gd>8){_G7=_Gb;return __continue;}else{var _Ge=_G4+E(_Gc.b)|0;if(_Ge<1){_G7=_Gb;return __continue;}else{if(_Ge>8){_G7=_Gb;return __continue;}else{var _Gf=B(_4i(_ED,_G4,_Gd,_Ge));if(!_Gf._){return E(_cr);}else{var _Gg=E(_Gf.b);if(!_Gg._){return E(_8I);}else{if(!B(_E5(B(_8D(_Gg.a,_Gg.b))))){_G7=_Gb;return __continue;}else{var _Gh=function(_Gi){while(1){var _Gj=E(_Gi);if(!_Gj._){return true;}else{var _Gk=_Gj.b,_Gl=E(_Gj.a),_Gm=E(_Gl.a);if(E(_Gm.a)!=_Gd){_Gi=_Gk;continue;}else{if(E(_Gm.b)!=_Ge){_Gi=_Gk;continue;}else{var _Gn=u_iswupper(E(_Gl.b));if(!E(_Gn)){return false;}else{_Gi=_Gk;continue;}}}}}};if(!B((function(_Go,_Gp){var _Gq=E(_Go),_Gr=E(_Gq.a);if(E(_Gr.a)!=_Gd){return new F(function(){return _Gh(_Gp);});}else{if(E(_Gr.b)!=_Ge){return new F(function(){return _Gh(_Gp);});}else{var _Gs=u_iswupper(E(_Gq.b));if(!E(_Gs)){return false;}else{return new F(function(){return _Gh(_Gp);});}}}})(_dC,_dD))){_G7=_Gb;return __continue;}else{var _Gt=new T(function(){var _Gu=function(_Gv){while(1){var _Gw=E(_Gv);if(!_Gw._){return false;}else{var _Gx=_Gw.b,_Gy=E(E(_Gw.a).a);if(E(_Gy.a)!=_Gd){_Gv=_Gx;continue;}else{if(E(_Gy.b)!=_Ge){_Gv=_Gx;continue;}else{return true;}}}}};if(!B((function(_Gz,_GA){var _GB=E(E(_Gz).a);if(E(_GB.a)!=_Gd){return new F(function(){return _Gu(_GA);});}else{if(E(_GB.b)!=_Ge){return new F(function(){return _Gu(_GA);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_GC=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_Gd)==8){if(E(_Ge)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_Gd)==1){if(E(_Ge)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_Ew))));}),_GD=new T(function(){var _GE=function(_GF){var _GG=E(_GF),_GH=E(_GG.a),_GI=_GH.b,_GJ=E(_GH.a),_GK=function(_GL){return (_GJ!=_ED)?true:(E(_GI)!=_G4)?true:(E(_GG.b)==114)?false:true;};if(_GJ!=_Gd){return new F(function(){return _GK(_);});}else{if(E(_GI)!=_Ge){return new F(function(){return _GK(_);});}else{return false;}}};return B(_5R(_GE,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_Gd,_Ge),_95),_GD),b:_5L,c:_GC,d:_ds,e:_Gt,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_G6(_Gb));}));}}}}}}}}}})(_G7));if(_G8!=__continue){return _G8;}}};return new F(function(){return _G6(_EA);});}else{if(_G5>8){var _GM=function(_GN){while(1){var _GO=B((function(_GP){var _GQ=E(_GP);if(!_GQ._){return E(_Ev);}else{var _GR=_GQ.b,_GS=E(_GQ.a),_GT=_ED+E(_GS.a)|0;if(_GT<1){_GN=_GR;return __continue;}else{if(_GT>8){_GN=_GR;return __continue;}else{var _GU=_G4+E(_GS.b)|0;if(_GU<1){_GN=_GR;return __continue;}else{if(_GU>8){_GN=_GR;return __continue;}else{var _GV=B(_4i(_ED,_G4,_GT,_GU));if(!_GV._){return E(_cr);}else{var _GW=E(_GV.b);if(!_GW._){return E(_8I);}else{if(!B(_E5(B(_8D(_GW.a,_GW.b))))){_GN=_GR;return __continue;}else{var _GX=function(_GY){while(1){var _GZ=E(_GY);if(!_GZ._){return true;}else{var _H0=_GZ.b,_H1=E(_GZ.a),_H2=E(_H1.a);if(E(_H2.a)!=_GT){_GY=_H0;continue;}else{if(E(_H2.b)!=_GU){_GY=_H0;continue;}else{var _H3=u_iswupper(E(_H1.b));if(!E(_H3)){return false;}else{_GY=_H0;continue;}}}}}};if(!B((function(_H4,_H5){var _H6=E(_H4),_H7=E(_H6.a);if(E(_H7.a)!=_GT){return new F(function(){return _GX(_H5);});}else{if(E(_H7.b)!=_GU){return new F(function(){return _GX(_H5);});}else{var _H8=u_iswupper(E(_H6.b));if(!E(_H8)){return false;}else{return new F(function(){return _GX(_H5);});}}}})(_dC,_dD))){_GN=_GR;return __continue;}else{var _H9=new T(function(){var _Ha=function(_Hb){while(1){var _Hc=E(_Hb);if(!_Hc._){return false;}else{var _Hd=_Hc.b,_He=E(E(_Hc.a).a);if(E(_He.a)!=_GT){_Hb=_Hd;continue;}else{if(E(_He.b)!=_GU){_Hb=_Hd;continue;}else{return true;}}}}};if(!B((function(_Hf,_Hg){var _Hh=E(E(_Hf).a);if(E(_Hh.a)!=_GT){return new F(function(){return _Ha(_Hg);});}else{if(E(_Hh.b)!=_GU){return new F(function(){return _Ha(_Hg);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_Hi=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_GT)==8){if(E(_GU)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_GT)==1){if(E(_GU)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_Ew))));}),_Hj=new T(function(){var _Hk=function(_Hl){var _Hm=E(_Hl),_Hn=E(_Hm.a),_Ho=_Hn.b,_Hp=E(_Hn.a),_Hq=function(_Hr){return (_Hp!=_ED)?true:(E(_Ho)!=_G4)?true:(E(_Hm.b)==114)?false:true;};if(_Hp!=_GT){return new F(function(){return _Hq(_);});}else{if(E(_Ho)!=_GU){return new F(function(){return _Hq(_);});}else{return false;}}};return B(_5R(_Hk,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_GT,_GU),_95),_Hj),b:_5L,c:_Hi,d:_ds,e:_H9,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_GM(_GR));}));}}}}}}}}}})(_GN));if(_GO!=__continue){return _GO;}}};return new F(function(){return _GM(_EA);});}else{var _Hs=B(_4i(_ED,_G4,_EF,_G5));if(!_Hs._){return E(_cr);}else{var _Ht=E(_Hs.b);if(!_Ht._){return E(_8I);}else{if(!B(_E5(B(_8D(_Ht.a,_Ht.b))))){var _Hu=function(_Hv){while(1){var _Hw=B((function(_Hx){var _Hy=E(_Hx);if(!_Hy._){return E(_Ev);}else{var _Hz=_Hy.b,_HA=E(_Hy.a),_HB=_ED+E(_HA.a)|0;if(_HB<1){_Hv=_Hz;return __continue;}else{if(_HB>8){_Hv=_Hz;return __continue;}else{var _HC=_G4+E(_HA.b)|0;if(_HC<1){_Hv=_Hz;return __continue;}else{if(_HC>8){_Hv=_Hz;return __continue;}else{var _HD=B(_4i(_ED,_G4,_HB,_HC));if(!_HD._){return E(_cr);}else{var _HE=E(_HD.b);if(!_HE._){return E(_8I);}else{if(!B(_E5(B(_8D(_HE.a,_HE.b))))){_Hv=_Hz;return __continue;}else{var _HF=function(_HG){while(1){var _HH=E(_HG);if(!_HH._){return true;}else{var _HI=_HH.b,_HJ=E(_HH.a),_HK=E(_HJ.a);if(E(_HK.a)!=_HB){_HG=_HI;continue;}else{if(E(_HK.b)!=_HC){_HG=_HI;continue;}else{var _HL=u_iswupper(E(_HJ.b));if(!E(_HL)){return false;}else{_HG=_HI;continue;}}}}}};if(!B((function(_HM,_HN){var _HO=E(_HM),_HP=E(_HO.a);if(E(_HP.a)!=_HB){return new F(function(){return _HF(_HN);});}else{if(E(_HP.b)!=_HC){return new F(function(){return _HF(_HN);});}else{var _HQ=u_iswupper(E(_HO.b));if(!E(_HQ)){return false;}else{return new F(function(){return _HF(_HN);});}}}})(_dC,_dD))){_Hv=_Hz;return __continue;}else{var _HR=new T(function(){var _HS=function(_HT){while(1){var _HU=E(_HT);if(!_HU._){return false;}else{var _HV=_HU.b,_HW=E(E(_HU.a).a);if(E(_HW.a)!=_HB){_HT=_HV;continue;}else{if(E(_HW.b)!=_HC){_HT=_HV;continue;}else{return true;}}}}};if(!B((function(_HX,_HY){var _HZ=E(E(_HX).a);if(E(_HZ.a)!=_HB){return new F(function(){return _HS(_HY);});}else{if(E(_HZ.b)!=_HC){return new F(function(){return _HS(_HY);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_I0=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_HB)==8){if(E(_HC)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_HB)==1){if(E(_HC)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_Ew))));}),_I1=new T(function(){var _I2=function(_I3){var _I4=E(_I3),_I5=E(_I4.a),_I6=_I5.b,_I7=E(_I5.a),_I8=function(_I9){return (_I7!=_ED)?true:(E(_I6)!=_G4)?true:(E(_I4.b)==114)?false:true;};if(_I7!=_HB){return new F(function(){return _I8(_);});}else{if(E(_I6)!=_HC){return new F(function(){return _I8(_);});}else{return false;}}};return B(_5R(_I2,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_HB,_HC),_95),_I1),b:_5L,c:_I0,d:_ds,e:_HR,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_Hu(_Hz));}));}}}}}}}}}})(_Hv));if(_Hw!=__continue){return _Hw;}}};return new F(function(){return _Hu(_EA);});}else{var _Ia=function(_Ib){while(1){var _Ic=E(_Ib);if(!_Ic._){return true;}else{var _Id=_Ic.b,_Ie=E(_Ic.a),_If=E(_Ie.a);if(E(_If.a)!=_EF){_Ib=_Id;continue;}else{if(E(_If.b)!=_G5){_Ib=_Id;continue;}else{var _Ig=u_iswupper(E(_Ie.b));if(!E(_Ig)){return false;}else{_Ib=_Id;continue;}}}}}};if(!B((function(_Ih,_Ii){var _Ij=E(_Ih),_Ik=E(_Ij.a);if(E(_Ik.a)!=_EF){return new F(function(){return _Ia(_Ii);});}else{if(E(_Ik.b)!=_G5){return new F(function(){return _Ia(_Ii);});}else{var _Il=u_iswupper(E(_Ij.b));if(!E(_Il)){return false;}else{return new F(function(){return _Ia(_Ii);});}}}})(_dC,_dD))){var _Im=function(_In){while(1){var _Io=B((function(_Ip){var _Iq=E(_Ip);if(!_Iq._){return E(_Ev);}else{var _Ir=_Iq.b,_Is=E(_Iq.a),_It=_ED+E(_Is.a)|0;if(_It<1){_In=_Ir;return __continue;}else{if(_It>8){_In=_Ir;return __continue;}else{var _Iu=_G4+E(_Is.b)|0;if(_Iu<1){_In=_Ir;return __continue;}else{if(_Iu>8){_In=_Ir;return __continue;}else{var _Iv=B(_4i(_ED,_G4,_It,_Iu));if(!_Iv._){return E(_cr);}else{var _Iw=E(_Iv.b);if(!_Iw._){return E(_8I);}else{if(!B(_E5(B(_8D(_Iw.a,_Iw.b))))){_In=_Ir;return __continue;}else{var _Ix=function(_Iy){while(1){var _Iz=E(_Iy);if(!_Iz._){return true;}else{var _IA=_Iz.b,_IB=E(_Iz.a),_IC=E(_IB.a);if(E(_IC.a)!=_It){_Iy=_IA;continue;}else{if(E(_IC.b)!=_Iu){_Iy=_IA;continue;}else{var _ID=u_iswupper(E(_IB.b));if(!E(_ID)){return false;}else{_Iy=_IA;continue;}}}}}};if(!B((function(_IE,_IF){var _IG=E(_IE),_IH=E(_IG.a);if(E(_IH.a)!=_It){return new F(function(){return _Ix(_IF);});}else{if(E(_IH.b)!=_Iu){return new F(function(){return _Ix(_IF);});}else{var _II=u_iswupper(E(_IG.b));if(!E(_II)){return false;}else{return new F(function(){return _Ix(_IF);});}}}})(_dC,_dD))){_In=_Ir;return __continue;}else{var _IJ=new T(function(){var _IK=function(_IL){while(1){var _IM=E(_IL);if(!_IM._){return false;}else{var _IN=_IM.b,_IO=E(E(_IM.a).a);if(E(_IO.a)!=_It){_IL=_IN;continue;}else{if(E(_IO.b)!=_Iu){_IL=_IN;continue;}else{return true;}}}}};if(!B((function(_IP,_IQ){var _IR=E(E(_IP).a);if(E(_IR.a)!=_It){return new F(function(){return _IK(_IQ);});}else{if(E(_IR.b)!=_Iu){return new F(function(){return _IK(_IQ);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_IS=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_It)==8){if(E(_Iu)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_It)==1){if(E(_Iu)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_Ew))));}),_IT=new T(function(){var _IU=function(_IV){var _IW=E(_IV),_IX=E(_IW.a),_IY=_IX.b,_IZ=E(_IX.a),_J0=function(_J1){return (_IZ!=_ED)?true:(E(_IY)!=_G4)?true:(E(_IW.b)==114)?false:true;};if(_IZ!=_It){return new F(function(){return _J0(_);});}else{if(E(_IY)!=_Iu){return new F(function(){return _J0(_);});}else{return false;}}};return B(_5R(_IU,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_It,_Iu),_95),_IT),b:_5L,c:_IS,d:_ds,e:_IJ,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_Im(_Ir));}));}}}}}}}}}})(_In));if(_Io!=__continue){return _Io;}}};return new F(function(){return _Im(_EA);});}else{var _J2=new T(function(){var _J3=function(_J4){while(1){var _J5=B((function(_J6){var _J7=E(_J6);if(!_J7._){return E(_Ev);}else{var _J8=_J7.b,_J9=E(_J7.a),_Ja=_ED+E(_J9.a)|0;if(_Ja<1){_J4=_J8;return __continue;}else{if(_Ja>8){_J4=_J8;return __continue;}else{var _Jb=_G4+E(_J9.b)|0;if(_Jb<1){_J4=_J8;return __continue;}else{if(_Jb>8){_J4=_J8;return __continue;}else{var _Jc=B(_4i(_ED,_G4,_Ja,_Jb));if(!_Jc._){return E(_cr);}else{var _Jd=E(_Jc.b);if(!_Jd._){return E(_8I);}else{if(!B(_E5(B(_8D(_Jd.a,_Jd.b))))){_J4=_J8;return __continue;}else{var _Je=function(_Jf){while(1){var _Jg=E(_Jf);if(!_Jg._){return true;}else{var _Jh=_Jg.b,_Ji=E(_Jg.a),_Jj=E(_Ji.a);if(E(_Jj.a)!=_Ja){_Jf=_Jh;continue;}else{if(E(_Jj.b)!=_Jb){_Jf=_Jh;continue;}else{var _Jk=u_iswupper(E(_Ji.b));if(!E(_Jk)){return false;}else{_Jf=_Jh;continue;}}}}}};if(!B((function(_Jl,_Jm){var _Jn=E(_Jl),_Jo=E(_Jn.a);if(E(_Jo.a)!=_Ja){return new F(function(){return _Je(_Jm);});}else{if(E(_Jo.b)!=_Jb){return new F(function(){return _Je(_Jm);});}else{var _Jp=u_iswupper(E(_Jn.b));if(!E(_Jp)){return false;}else{return new F(function(){return _Je(_Jm);});}}}})(_dC,_dD))){_J4=_J8;return __continue;}else{var _Jq=new T(function(){var _Jr=function(_Js){while(1){var _Jt=E(_Js);if(!_Jt._){return false;}else{var _Ju=_Jt.b,_Jv=E(E(_Jt.a).a);if(E(_Jv.a)!=_Ja){_Js=_Ju;continue;}else{if(E(_Jv.b)!=_Jb){_Js=_Ju;continue;}else{return true;}}}}};if(!B((function(_Jw,_Jx){var _Jy=E(E(_Jw).a);if(E(_Jy.a)!=_Ja){return new F(function(){return _Jr(_Jx);});}else{if(E(_Jy.b)!=_Jb){return new F(function(){return _Jr(_Jx);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_Jz=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_Ja)==8){if(E(_Jb)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_Ja)==1){if(E(_Jb)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_Ew))));}),_JA=new T(function(){var _JB=function(_JC){var _JD=E(_JC),_JE=E(_JD.a),_JF=_JE.b,_JG=E(_JE.a),_JH=function(_JI){return (_JG!=_ED)?true:(E(_JF)!=_G4)?true:(E(_JD.b)==114)?false:true;};if(_JG!=_Ja){return new F(function(){return _JH(_);});}else{if(E(_JF)!=_Jb){return new F(function(){return _JH(_);});}else{return false;}}};return B(_5R(_JB,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_Ja,_Jb),_95),_JA),b:_5L,c:_Jz,d:_ds,e:_Jq,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_J3(_J8));}));}}}}}}}}}})(_J4));if(_J5!=__continue){return _J5;}}};return B(_J3(_EA));}),_JJ=new T(function(){var _JK=function(_JL){while(1){var _JM=E(_JL);if(!_JM._){return false;}else{var _JN=_JM.b,_JO=E(E(_JM.a).a);if(E(_JO.a)!=_EF){_JL=_JN;continue;}else{if(E(_JO.b)!=_G5){_JL=_JN;continue;}else{return true;}}}}};if(!B((function(_JP,_JQ){var _JR=E(E(_JP).a);if(E(_JR.a)!=_EF){return new F(function(){return _JK(_JQ);});}else{if(E(_JR.b)!=_G5){return new F(function(){return _JK(_JQ);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_JS=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_EF)==8){if(E(_G5)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_EF)==1){if(E(_G5)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_Ew))));}),_JT=new T(function(){var _JU=function(_JV){var _JW=E(_JV),_JX=E(_JW.a),_JY=_JX.b,_JZ=E(_JX.a),_K0=function(_K1){return (_JZ!=_ED)?true:(E(_JY)!=_G4)?true:(E(_JW.b)==114)?false:true;};if(_JZ!=_EF){return new F(function(){return _K0(_);});}else{if(E(_JY)!=_G5){return new F(function(){return _K0(_);});}else{return false;}}};return B(_5R(_JU,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_EF,_G5),_95),_JT),b:_5L,c:_JS,d:_ds,e:_JJ,f:_8S,g:_8L,h:_8L,i:_5K},_J2);}}}}}}}}}}else{return E(_Ev);}}},_K2=function(_K3,_K4){var _K5=E(_K3),_K6=_K5.a,_K7=new T(function(){return B(_Eq(_K4));});if(E(_K5.b)==114){var _K8=new T(function(){return B(_5B(2,new T(function(){var _K9=E(_K6);if(E(_K9.a)==8){if(E(_K9.b)==8){return true;}else{return E(_dy);}}else{return E(_dy);}}),B(_5B(3,new T(function(){var _Ka=E(_K6);if(E(_Ka.a)==1){if(E(_Ka.b)==8){return true;}else{return E(_dx);}}else{return E(_dx);}}),_dr))));}),_Kb=E(_cg);if(!_Kb._){return E(_K7);}else{var _Kc=_Kb.b,_Kd=E(_K6),_Ke=_Kd.b,_Kf=E(_Kd.a),_Kg=E(_Kb.a),_Kh=_Kf+E(_Kg.a)|0;if(_Kh<1){var _Ki=function(_Kj){while(1){var _Kk=B((function(_Kl){var _Km=E(_Kl);if(!_Km._){return E(_K7);}else{var _Kn=_Km.b,_Ko=E(_Km.a),_Kp=_Kf+E(_Ko.a)|0;if(_Kp<1){_Kj=_Kn;return __continue;}else{if(_Kp>8){_Kj=_Kn;return __continue;}else{var _Kq=E(_Ke),_Kr=_Kq+E(_Ko.b)|0;if(_Kr<1){_Kj=_Kn;return __continue;}else{if(_Kr>8){_Kj=_Kn;return __continue;}else{var _Ks=B(_4i(_Kf,_Kq,_Kp,_Kr));if(!_Ks._){return E(_cr);}else{var _Kt=E(_Ks.b);if(!_Kt._){return E(_8I);}else{if(!B(_E5(B(_8D(_Kt.a,_Kt.b))))){_Kj=_Kn;return __continue;}else{var _Ku=function(_Kv){while(1){var _Kw=E(_Kv);if(!_Kw._){return true;}else{var _Kx=_Kw.b,_Ky=E(_Kw.a),_Kz=E(_Ky.a);if(E(_Kz.a)!=_Kp){_Kv=_Kx;continue;}else{if(E(_Kz.b)!=_Kr){_Kv=_Kx;continue;}else{var _KA=u_iswupper(E(_Ky.b));if(!E(_KA)){return false;}else{_Kv=_Kx;continue;}}}}}};if(!B((function(_KB,_KC){var _KD=E(_KB),_KE=E(_KD.a);if(E(_KE.a)!=_Kp){return new F(function(){return _Ku(_KC);});}else{if(E(_KE.b)!=_Kr){return new F(function(){return _Ku(_KC);});}else{var _KF=u_iswupper(E(_KD.b));if(!E(_KF)){return false;}else{return new F(function(){return _Ku(_KC);});}}}})(_dC,_dD))){_Kj=_Kn;return __continue;}else{var _KG=new T(function(){var _KH=function(_KI){while(1){var _KJ=E(_KI);if(!_KJ._){return false;}else{var _KK=_KJ.b,_KL=E(E(_KJ.a).a);if(E(_KL.a)!=_Kp){_KI=_KK;continue;}else{if(E(_KL.b)!=_Kr){_KI=_KK;continue;}else{return true;}}}}};if(!B((function(_KM,_KN){var _KO=E(E(_KM).a);if(E(_KO.a)!=_Kp){return new F(function(){return _KH(_KN);});}else{if(E(_KO.b)!=_Kr){return new F(function(){return _KH(_KN);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_KP=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_Kp)==8){if(E(_Kr)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_Kp)==1){if(E(_Kr)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_K8))));}),_KQ=new T(function(){var _KR=function(_KS){var _KT=E(_KS),_KU=E(_KT.a),_KV=_KU.b,_KW=E(_KU.a),_KX=function(_KY){return (_KW!=_Kf)?true:(E(_KV)!=_Kq)?true:(E(_KT.b)==114)?false:true;};if(_KW!=_Kp){return new F(function(){return _KX(_);});}else{if(E(_KV)!=_Kr){return new F(function(){return _KX(_);});}else{return false;}}};return B(_5R(_KR,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_Kp,_Kr),_95),_KQ),b:_5L,c:_KP,d:_ds,e:_KG,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_Ki(_Kn));}));}}}}}}}}}})(_Kj));if(_Kk!=__continue){return _Kk;}}};return new F(function(){return _Ki(_Kc);});}else{if(_Kh>8){var _KZ=function(_L0){while(1){var _L1=B((function(_L2){var _L3=E(_L2);if(!_L3._){return E(_K7);}else{var _L4=_L3.b,_L5=E(_L3.a),_L6=_Kf+E(_L5.a)|0;if(_L6<1){_L0=_L4;return __continue;}else{if(_L6>8){_L0=_L4;return __continue;}else{var _L7=E(_Ke),_L8=_L7+E(_L5.b)|0;if(_L8<1){_L0=_L4;return __continue;}else{if(_L8>8){_L0=_L4;return __continue;}else{var _L9=B(_4i(_Kf,_L7,_L6,_L8));if(!_L9._){return E(_cr);}else{var _La=E(_L9.b);if(!_La._){return E(_8I);}else{if(!B(_E5(B(_8D(_La.a,_La.b))))){_L0=_L4;return __continue;}else{var _Lb=function(_Lc){while(1){var _Ld=E(_Lc);if(!_Ld._){return true;}else{var _Le=_Ld.b,_Lf=E(_Ld.a),_Lg=E(_Lf.a);if(E(_Lg.a)!=_L6){_Lc=_Le;continue;}else{if(E(_Lg.b)!=_L8){_Lc=_Le;continue;}else{var _Lh=u_iswupper(E(_Lf.b));if(!E(_Lh)){return false;}else{_Lc=_Le;continue;}}}}}};if(!B((function(_Li,_Lj){var _Lk=E(_Li),_Ll=E(_Lk.a);if(E(_Ll.a)!=_L6){return new F(function(){return _Lb(_Lj);});}else{if(E(_Ll.b)!=_L8){return new F(function(){return _Lb(_Lj);});}else{var _Lm=u_iswupper(E(_Lk.b));if(!E(_Lm)){return false;}else{return new F(function(){return _Lb(_Lj);});}}}})(_dC,_dD))){_L0=_L4;return __continue;}else{var _Ln=new T(function(){var _Lo=function(_Lp){while(1){var _Lq=E(_Lp);if(!_Lq._){return false;}else{var _Lr=_Lq.b,_Ls=E(E(_Lq.a).a);if(E(_Ls.a)!=_L6){_Lp=_Lr;continue;}else{if(E(_Ls.b)!=_L8){_Lp=_Lr;continue;}else{return true;}}}}};if(!B((function(_Lt,_Lu){var _Lv=E(E(_Lt).a);if(E(_Lv.a)!=_L6){return new F(function(){return _Lo(_Lu);});}else{if(E(_Lv.b)!=_L8){return new F(function(){return _Lo(_Lu);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_Lw=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_L6)==8){if(E(_L8)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_L6)==1){if(E(_L8)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_K8))));}),_Lx=new T(function(){var _Ly=function(_Lz){var _LA=E(_Lz),_LB=E(_LA.a),_LC=_LB.b,_LD=E(_LB.a),_LE=function(_LF){return (_LD!=_Kf)?true:(E(_LC)!=_L7)?true:(E(_LA.b)==114)?false:true;};if(_LD!=_L6){return new F(function(){return _LE(_);});}else{if(E(_LC)!=_L8){return new F(function(){return _LE(_);});}else{return false;}}};return B(_5R(_Ly,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_L6,_L8),_95),_Lx),b:_5L,c:_Lw,d:_ds,e:_Ln,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_KZ(_L4));}));}}}}}}}}}})(_L0));if(_L1!=__continue){return _L1;}}};return new F(function(){return _KZ(_Kc);});}else{var _LG=E(_Ke),_LH=_LG+E(_Kg.b)|0;if(_LH<1){var _LI=function(_LJ){while(1){var _LK=B((function(_LL){var _LM=E(_LL);if(!_LM._){return E(_K7);}else{var _LN=_LM.b,_LO=E(_LM.a),_LP=_Kf+E(_LO.a)|0;if(_LP<1){_LJ=_LN;return __continue;}else{if(_LP>8){_LJ=_LN;return __continue;}else{var _LQ=_LG+E(_LO.b)|0;if(_LQ<1){_LJ=_LN;return __continue;}else{if(_LQ>8){_LJ=_LN;return __continue;}else{var _LR=B(_4i(_Kf,_LG,_LP,_LQ));if(!_LR._){return E(_cr);}else{var _LS=E(_LR.b);if(!_LS._){return E(_8I);}else{if(!B(_E5(B(_8D(_LS.a,_LS.b))))){_LJ=_LN;return __continue;}else{var _LT=function(_LU){while(1){var _LV=E(_LU);if(!_LV._){return true;}else{var _LW=_LV.b,_LX=E(_LV.a),_LY=E(_LX.a);if(E(_LY.a)!=_LP){_LU=_LW;continue;}else{if(E(_LY.b)!=_LQ){_LU=_LW;continue;}else{var _LZ=u_iswupper(E(_LX.b));if(!E(_LZ)){return false;}else{_LU=_LW;continue;}}}}}};if(!B((function(_M0,_M1){var _M2=E(_M0),_M3=E(_M2.a);if(E(_M3.a)!=_LP){return new F(function(){return _LT(_M1);});}else{if(E(_M3.b)!=_LQ){return new F(function(){return _LT(_M1);});}else{var _M4=u_iswupper(E(_M2.b));if(!E(_M4)){return false;}else{return new F(function(){return _LT(_M1);});}}}})(_dC,_dD))){_LJ=_LN;return __continue;}else{var _M5=new T(function(){var _M6=function(_M7){while(1){var _M8=E(_M7);if(!_M8._){return false;}else{var _M9=_M8.b,_Ma=E(E(_M8.a).a);if(E(_Ma.a)!=_LP){_M7=_M9;continue;}else{if(E(_Ma.b)!=_LQ){_M7=_M9;continue;}else{return true;}}}}};if(!B((function(_Mb,_Mc){var _Md=E(E(_Mb).a);if(E(_Md.a)!=_LP){return new F(function(){return _M6(_Mc);});}else{if(E(_Md.b)!=_LQ){return new F(function(){return _M6(_Mc);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_Me=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_LP)==8){if(E(_LQ)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_LP)==1){if(E(_LQ)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_K8))));}),_Mf=new T(function(){var _Mg=function(_Mh){var _Mi=E(_Mh),_Mj=E(_Mi.a),_Mk=_Mj.b,_Ml=E(_Mj.a),_Mm=function(_Mn){return (_Ml!=_Kf)?true:(E(_Mk)!=_LG)?true:(E(_Mi.b)==114)?false:true;};if(_Ml!=_LP){return new F(function(){return _Mm(_);});}else{if(E(_Mk)!=_LQ){return new F(function(){return _Mm(_);});}else{return false;}}};return B(_5R(_Mg,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_LP,_LQ),_95),_Mf),b:_5L,c:_Me,d:_ds,e:_M5,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_LI(_LN));}));}}}}}}}}}})(_LJ));if(_LK!=__continue){return _LK;}}};return new F(function(){return _LI(_Kc);});}else{if(_LH>8){var _Mo=function(_Mp){while(1){var _Mq=B((function(_Mr){var _Ms=E(_Mr);if(!_Ms._){return E(_K7);}else{var _Mt=_Ms.b,_Mu=E(_Ms.a),_Mv=_Kf+E(_Mu.a)|0;if(_Mv<1){_Mp=_Mt;return __continue;}else{if(_Mv>8){_Mp=_Mt;return __continue;}else{var _Mw=_LG+E(_Mu.b)|0;if(_Mw<1){_Mp=_Mt;return __continue;}else{if(_Mw>8){_Mp=_Mt;return __continue;}else{var _Mx=B(_4i(_Kf,_LG,_Mv,_Mw));if(!_Mx._){return E(_cr);}else{var _My=E(_Mx.b);if(!_My._){return E(_8I);}else{if(!B(_E5(B(_8D(_My.a,_My.b))))){_Mp=_Mt;return __continue;}else{var _Mz=function(_MA){while(1){var _MB=E(_MA);if(!_MB._){return true;}else{var _MC=_MB.b,_MD=E(_MB.a),_ME=E(_MD.a);if(E(_ME.a)!=_Mv){_MA=_MC;continue;}else{if(E(_ME.b)!=_Mw){_MA=_MC;continue;}else{var _MF=u_iswupper(E(_MD.b));if(!E(_MF)){return false;}else{_MA=_MC;continue;}}}}}};if(!B((function(_MG,_MH){var _MI=E(_MG),_MJ=E(_MI.a);if(E(_MJ.a)!=_Mv){return new F(function(){return _Mz(_MH);});}else{if(E(_MJ.b)!=_Mw){return new F(function(){return _Mz(_MH);});}else{var _MK=u_iswupper(E(_MI.b));if(!E(_MK)){return false;}else{return new F(function(){return _Mz(_MH);});}}}})(_dC,_dD))){_Mp=_Mt;return __continue;}else{var _ML=new T(function(){var _MM=function(_MN){while(1){var _MO=E(_MN);if(!_MO._){return false;}else{var _MP=_MO.b,_MQ=E(E(_MO.a).a);if(E(_MQ.a)!=_Mv){_MN=_MP;continue;}else{if(E(_MQ.b)!=_Mw){_MN=_MP;continue;}else{return true;}}}}};if(!B((function(_MR,_MS){var _MT=E(E(_MR).a);if(E(_MT.a)!=_Mv){return new F(function(){return _MM(_MS);});}else{if(E(_MT.b)!=_Mw){return new F(function(){return _MM(_MS);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_MU=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_Mv)==8){if(E(_Mw)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_Mv)==1){if(E(_Mw)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_K8))));}),_MV=new T(function(){var _MW=function(_MX){var _MY=E(_MX),_MZ=E(_MY.a),_N0=_MZ.b,_N1=E(_MZ.a),_N2=function(_N3){return (_N1!=_Kf)?true:(E(_N0)!=_LG)?true:(E(_MY.b)==114)?false:true;};if(_N1!=_Mv){return new F(function(){return _N2(_);});}else{if(E(_N0)!=_Mw){return new F(function(){return _N2(_);});}else{return false;}}};return B(_5R(_MW,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_Mv,_Mw),_95),_MV),b:_5L,c:_MU,d:_ds,e:_ML,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_Mo(_Mt));}));}}}}}}}}}})(_Mp));if(_Mq!=__continue){return _Mq;}}};return new F(function(){return _Mo(_Kc);});}else{var _N4=B(_4i(_Kf,_LG,_Kh,_LH));if(!_N4._){return E(_cr);}else{var _N5=E(_N4.b);if(!_N5._){return E(_8I);}else{if(!B(_E5(B(_8D(_N5.a,_N5.b))))){var _N6=function(_N7){while(1){var _N8=B((function(_N9){var _Na=E(_N9);if(!_Na._){return E(_K7);}else{var _Nb=_Na.b,_Nc=E(_Na.a),_Nd=_Kf+E(_Nc.a)|0;if(_Nd<1){_N7=_Nb;return __continue;}else{if(_Nd>8){_N7=_Nb;return __continue;}else{var _Ne=_LG+E(_Nc.b)|0;if(_Ne<1){_N7=_Nb;return __continue;}else{if(_Ne>8){_N7=_Nb;return __continue;}else{var _Nf=B(_4i(_Kf,_LG,_Nd,_Ne));if(!_Nf._){return E(_cr);}else{var _Ng=E(_Nf.b);if(!_Ng._){return E(_8I);}else{if(!B(_E5(B(_8D(_Ng.a,_Ng.b))))){_N7=_Nb;return __continue;}else{var _Nh=function(_Ni){while(1){var _Nj=E(_Ni);if(!_Nj._){return true;}else{var _Nk=_Nj.b,_Nl=E(_Nj.a),_Nm=E(_Nl.a);if(E(_Nm.a)!=_Nd){_Ni=_Nk;continue;}else{if(E(_Nm.b)!=_Ne){_Ni=_Nk;continue;}else{var _Nn=u_iswupper(E(_Nl.b));if(!E(_Nn)){return false;}else{_Ni=_Nk;continue;}}}}}};if(!B((function(_No,_Np){var _Nq=E(_No),_Nr=E(_Nq.a);if(E(_Nr.a)!=_Nd){return new F(function(){return _Nh(_Np);});}else{if(E(_Nr.b)!=_Ne){return new F(function(){return _Nh(_Np);});}else{var _Ns=u_iswupper(E(_Nq.b));if(!E(_Ns)){return false;}else{return new F(function(){return _Nh(_Np);});}}}})(_dC,_dD))){_N7=_Nb;return __continue;}else{var _Nt=new T(function(){var _Nu=function(_Nv){while(1){var _Nw=E(_Nv);if(!_Nw._){return false;}else{var _Nx=_Nw.b,_Ny=E(E(_Nw.a).a);if(E(_Ny.a)!=_Nd){_Nv=_Nx;continue;}else{if(E(_Ny.b)!=_Ne){_Nv=_Nx;continue;}else{return true;}}}}};if(!B((function(_Nz,_NA){var _NB=E(E(_Nz).a);if(E(_NB.a)!=_Nd){return new F(function(){return _Nu(_NA);});}else{if(E(_NB.b)!=_Ne){return new F(function(){return _Nu(_NA);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_NC=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_Nd)==8){if(E(_Ne)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_Nd)==1){if(E(_Ne)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_K8))));}),_ND=new T(function(){var _NE=function(_NF){var _NG=E(_NF),_NH=E(_NG.a),_NI=_NH.b,_NJ=E(_NH.a),_NK=function(_NL){return (_NJ!=_Kf)?true:(E(_NI)!=_LG)?true:(E(_NG.b)==114)?false:true;};if(_NJ!=_Nd){return new F(function(){return _NK(_);});}else{if(E(_NI)!=_Ne){return new F(function(){return _NK(_);});}else{return false;}}};return B(_5R(_NE,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_Nd,_Ne),_95),_ND),b:_5L,c:_NC,d:_ds,e:_Nt,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_N6(_Nb));}));}}}}}}}}}})(_N7));if(_N8!=__continue){return _N8;}}};return new F(function(){return _N6(_Kc);});}else{var _NM=function(_NN){while(1){var _NO=E(_NN);if(!_NO._){return true;}else{var _NP=_NO.b,_NQ=E(_NO.a),_NR=E(_NQ.a);if(E(_NR.a)!=_Kh){_NN=_NP;continue;}else{if(E(_NR.b)!=_LH){_NN=_NP;continue;}else{var _NS=u_iswupper(E(_NQ.b));if(!E(_NS)){return false;}else{_NN=_NP;continue;}}}}}};if(!B((function(_NT,_NU){var _NV=E(_NT),_NW=E(_NV.a);if(E(_NW.a)!=_Kh){return new F(function(){return _NM(_NU);});}else{if(E(_NW.b)!=_LH){return new F(function(){return _NM(_NU);});}else{var _NX=u_iswupper(E(_NV.b));if(!E(_NX)){return false;}else{return new F(function(){return _NM(_NU);});}}}})(_dC,_dD))){var _NY=function(_NZ){while(1){var _O0=B((function(_O1){var _O2=E(_O1);if(!_O2._){return E(_K7);}else{var _O3=_O2.b,_O4=E(_O2.a),_O5=_Kf+E(_O4.a)|0;if(_O5<1){_NZ=_O3;return __continue;}else{if(_O5>8){_NZ=_O3;return __continue;}else{var _O6=_LG+E(_O4.b)|0;if(_O6<1){_NZ=_O3;return __continue;}else{if(_O6>8){_NZ=_O3;return __continue;}else{var _O7=B(_4i(_Kf,_LG,_O5,_O6));if(!_O7._){return E(_cr);}else{var _O8=E(_O7.b);if(!_O8._){return E(_8I);}else{if(!B(_E5(B(_8D(_O8.a,_O8.b))))){_NZ=_O3;return __continue;}else{var _O9=function(_Oa){while(1){var _Ob=E(_Oa);if(!_Ob._){return true;}else{var _Oc=_Ob.b,_Od=E(_Ob.a),_Oe=E(_Od.a);if(E(_Oe.a)!=_O5){_Oa=_Oc;continue;}else{if(E(_Oe.b)!=_O6){_Oa=_Oc;continue;}else{var _Of=u_iswupper(E(_Od.b));if(!E(_Of)){return false;}else{_Oa=_Oc;continue;}}}}}};if(!B((function(_Og,_Oh){var _Oi=E(_Og),_Oj=E(_Oi.a);if(E(_Oj.a)!=_O5){return new F(function(){return _O9(_Oh);});}else{if(E(_Oj.b)!=_O6){return new F(function(){return _O9(_Oh);});}else{var _Ok=u_iswupper(E(_Oi.b));if(!E(_Ok)){return false;}else{return new F(function(){return _O9(_Oh);});}}}})(_dC,_dD))){_NZ=_O3;return __continue;}else{var _Ol=new T(function(){var _Om=function(_On){while(1){var _Oo=E(_On);if(!_Oo._){return false;}else{var _Op=_Oo.b,_Oq=E(E(_Oo.a).a);if(E(_Oq.a)!=_O5){_On=_Op;continue;}else{if(E(_Oq.b)!=_O6){_On=_Op;continue;}else{return true;}}}}};if(!B((function(_Or,_Os){var _Ot=E(E(_Or).a);if(E(_Ot.a)!=_O5){return new F(function(){return _Om(_Os);});}else{if(E(_Ot.b)!=_O6){return new F(function(){return _Om(_Os);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_Ou=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_O5)==8){if(E(_O6)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_O5)==1){if(E(_O6)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_K8))));}),_Ov=new T(function(){var _Ow=function(_Ox){var _Oy=E(_Ox),_Oz=E(_Oy.a),_OA=_Oz.b,_OB=E(_Oz.a),_OC=function(_OD){return (_OB!=_Kf)?true:(E(_OA)!=_LG)?true:(E(_Oy.b)==114)?false:true;};if(_OB!=_O5){return new F(function(){return _OC(_);});}else{if(E(_OA)!=_O6){return new F(function(){return _OC(_);});}else{return false;}}};return B(_5R(_Ow,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_O5,_O6),_95),_Ov),b:_5L,c:_Ou,d:_ds,e:_Ol,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_NY(_O3));}));}}}}}}}}}})(_NZ));if(_O0!=__continue){return _O0;}}};return new F(function(){return _NY(_Kc);});}else{var _OE=new T(function(){var _OF=function(_OG){while(1){var _OH=B((function(_OI){var _OJ=E(_OI);if(!_OJ._){return E(_K7);}else{var _OK=_OJ.b,_OL=E(_OJ.a),_OM=_Kf+E(_OL.a)|0;if(_OM<1){_OG=_OK;return __continue;}else{if(_OM>8){_OG=_OK;return __continue;}else{var _ON=_LG+E(_OL.b)|0;if(_ON<1){_OG=_OK;return __continue;}else{if(_ON>8){_OG=_OK;return __continue;}else{var _OO=B(_4i(_Kf,_LG,_OM,_ON));if(!_OO._){return E(_cr);}else{var _OP=E(_OO.b);if(!_OP._){return E(_8I);}else{if(!B(_E5(B(_8D(_OP.a,_OP.b))))){_OG=_OK;return __continue;}else{var _OQ=function(_OR){while(1){var _OS=E(_OR);if(!_OS._){return true;}else{var _OT=_OS.b,_OU=E(_OS.a),_OV=E(_OU.a);if(E(_OV.a)!=_OM){_OR=_OT;continue;}else{if(E(_OV.b)!=_ON){_OR=_OT;continue;}else{var _OW=u_iswupper(E(_OU.b));if(!E(_OW)){return false;}else{_OR=_OT;continue;}}}}}};if(!B((function(_OX,_OY){var _OZ=E(_OX),_P0=E(_OZ.a);if(E(_P0.a)!=_OM){return new F(function(){return _OQ(_OY);});}else{if(E(_P0.b)!=_ON){return new F(function(){return _OQ(_OY);});}else{var _P1=u_iswupper(E(_OZ.b));if(!E(_P1)){return false;}else{return new F(function(){return _OQ(_OY);});}}}})(_dC,_dD))){_OG=_OK;return __continue;}else{var _P2=new T(function(){var _P3=function(_P4){while(1){var _P5=E(_P4);if(!_P5._){return false;}else{var _P6=_P5.b,_P7=E(E(_P5.a).a);if(E(_P7.a)!=_OM){_P4=_P6;continue;}else{if(E(_P7.b)!=_ON){_P4=_P6;continue;}else{return true;}}}}};if(!B((function(_P8,_P9){var _Pa=E(E(_P8).a);if(E(_Pa.a)!=_OM){return new F(function(){return _P3(_P9);});}else{if(E(_Pa.b)!=_ON){return new F(function(){return _P3(_P9);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_Pb=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_OM)==8){if(E(_ON)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_OM)==1){if(E(_ON)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_K8))));}),_Pc=new T(function(){var _Pd=function(_Pe){var _Pf=E(_Pe),_Pg=E(_Pf.a),_Ph=_Pg.b,_Pi=E(_Pg.a),_Pj=function(_Pk){return (_Pi!=_Kf)?true:(E(_Ph)!=_LG)?true:(E(_Pf.b)==114)?false:true;};if(_Pi!=_OM){return new F(function(){return _Pj(_);});}else{if(E(_Ph)!=_ON){return new F(function(){return _Pj(_);});}else{return false;}}};return B(_5R(_Pd,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_OM,_ON),_95),_Pc),b:_5L,c:_Pb,d:_ds,e:_P2,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_OF(_OK));}));}}}}}}}}}})(_OG));if(_OH!=__continue){return _OH;}}};return B(_OF(_Kc));}),_Pl=new T(function(){var _Pm=function(_Pn){while(1){var _Po=E(_Pn);if(!_Po._){return false;}else{var _Pp=_Po.b,_Pq=E(E(_Po.a).a);if(E(_Pq.a)!=_Kh){_Pn=_Pp;continue;}else{if(E(_Pq.b)!=_LH){_Pn=_Pp;continue;}else{return true;}}}}};if(!B((function(_Pr,_Ps){var _Pt=E(E(_Pr).a);if(E(_Pt.a)!=_Kh){return new F(function(){return _Pm(_Ps);});}else{if(E(_Pt.b)!=_LH){return new F(function(){return _Pm(_Ps);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_Pu=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_Kh)==8){if(E(_LH)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_Kh)==1){if(E(_LH)==1){return true;}else{return false;}}else{return false;}}else{return true;}}),_K8))));}),_Pv=new T(function(){var _Pw=function(_Px){var _Py=E(_Px),_Pz=E(_Py.a),_PA=_Pz.b,_PB=E(_Pz.a),_PC=function(_PD){return (_PB!=_Kf)?true:(E(_PA)!=_LG)?true:(E(_Py.b)==114)?false:true;};if(_PB!=_Kh){return new F(function(){return _PC(_);});}else{if(E(_PA)!=_LH){return new F(function(){return _PC(_);});}else{return false;}}};return B(_5R(_Pw,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_Kh,_LH),_95),_Pv),b:_5L,c:_Pu,d:_ds,e:_Pl,f:_8S,g:_8L,h:_8L,i:_5K},_OE);}}}}}}}}}}else{return E(_K7);}};return B(_K2(_dC,_dD));}),_PE=function(_PF){while(1){var _PG=B((function(_PH){var _PI=E(_PH);if(!_PI._){return E(_eN);}else{var _PJ=_PI.b,_PK=E(_PI.a),_PL=_PK.a;if(E(_PK.b)==112){var _PM=new T(function(){return E(E(_PL).b)-1|0;}),_PN=function(_PO,_PP){var _PQ=E(_du),_PR=E(_PL),_PS=E(_PR.a),_PT=_PS+_PO|0;if(_PT!=E(_PQ.a)){return E(_PP);}else{var _PU=E(_PM);if(_PU!=E(_PQ.b)){return E(_PP);}else{var _PV=new T(function(){var _PW=function(_PX){var _PY=E(_PX),_PZ=E(_PY.a),_Q0=_PZ.b,_Q1=E(_PZ.a),_Q2=function(_Q3){return (_Q1!=_PS)?true:(E(_Q0)!=E(_PR.b))?true:(E(_PY.b)==112)?false:true;};if(_Q1!=_PT){return new F(function(){return _Q2(_);});}else{if(E(_Q0)!=(_PU+1|0)){return new F(function(){return _Q2(_);});}else{return false;}}};return B(_5R(_PW,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_PT,_PU),_ch),_PV),b:_5L,c:_dr,d:_ds,e:_8U,f:_8S,g:_8L,h:_8L,i:_5K},_PP);}}},_Q4=new T(function(){return B(_PN(1,new T(function(){return B(_PE(_PJ));})));});return new F(function(){return _PN(-1,_Q4);});}else{_PF=_PJ;return __continue;}}})(_PF));if(_PG!=__continue){return _PG;}}},_Q5=function(_Q6,_Q7){var _Q8=E(_Q6),_Q9=_Q8.a;if(E(_Q8.b)==112){var _Qa=new T(function(){return E(E(_Q9).b)-1|0;}),_Qb=function(_Qc,_Qd){var _Qe=E(_du),_Qf=E(_Q9),_Qg=E(_Qf.a),_Qh=_Qg+_Qc|0;if(_Qh!=E(_Qe.a)){return E(_Qd);}else{var _Qi=E(_Qa);if(_Qi!=E(_Qe.b)){return E(_Qd);}else{var _Qj=new T(function(){var _Qk=function(_Ql){var _Qm=E(_Ql),_Qn=E(_Qm.a),_Qo=_Qn.b,_Qp=E(_Qn.a),_Qq=function(_Qr){return (_Qp!=_Qg)?true:(E(_Qo)!=E(_Qf.b))?true:(E(_Qm.b)==112)?false:true;};if(_Qp!=_Qh){return new F(function(){return _Qq(_);});}else{if(E(_Qo)!=(_Qi+1|0)){return new F(function(){return _Qq(_);});}else{return false;}}};return B(_5R(_Qk,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_Qh,_Qi),_ch),_Qj),b:_5L,c:_dr,d:_ds,e:_8U,f:_8S,g:_8L,h:_8L,i:_5K},_Qd);}}},_Qs=new T(function(){return B(_Qb(1,new T(function(){return B(_PE(_Q7));})));});return new F(function(){return _Qb(-1,_Qs);});}else{return new F(function(){return _PE(_Q7);});}};return B(_Q5(_dC,_dD));}),_Qt=function(_Qu){while(1){var _Qv=B((function(_Qw){var _Qx=E(_Qw);if(!_Qx._){return E(_eM);}else{var _Qy=_Qx.b,_Qz=E(_Qx.a),_QA=_Qz.a;if(E(_Qz.b)==112){var _QB=new T(function(){return E(E(_QA).b)-1|0;}),_QC=function(_QD,_QE){var _QF=E(_QA),_QG=_QF.b,_QH=E(_QF.a),_QI=_QH+_QD|0;if(_QI<1){return E(_QE);}else{if(_QI>8){return E(_QE);}else{var _QJ=E(_QB);if(_QJ<1){return E(_QE);}else{if(_QJ>8){return E(_QE);}else{var _QK=function(_QL){while(1){var _QM=E(_QL);if(!_QM._){return false;}else{var _QN=_QM.b,_QO=E(_QM.a),_QP=E(_QO.a);if(E(_QP.a)!=_QI){_QL=_QN;continue;}else{if(E(_QP.b)!=_QJ){_QL=_QN;continue;}else{var _QQ=u_iswupper(E(_QO.b));if(!E(_QQ)){_QL=_QN;continue;}else{return true;}}}}}};if(!B((function(_QR,_QS){var _QT=E(_QR),_QU=E(_QT.a);if(E(_QU.a)!=_QI){return new F(function(){return _QK(_QS);});}else{if(E(_QU.b)!=_QJ){return new F(function(){return _QK(_QS);});}else{var _QV=u_iswupper(E(_QT.b));if(!E(_QV)){return new F(function(){return _QK(_QS);});}else{return true;}}}})(_dC,_dD))){return E(_QE);}else{var _QW=new T2(0,_QI,_QJ),_QX=E(_QJ);if(_QX==1){var _QY=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_QI)==8){return true;}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_QI)==1){return true;}else{return false;}}else{return true;}}),_dr))));}),_QZ=new T(function(){var _R0=function(_R1){var _R2=E(_R1),_R3=E(_R2.a),_R4=_R3.b,_R5=E(_R3.a),_R6=function(_R7){return (_R5!=_QH)?true:(E(_R4)!=E(_QG))?true:(E(_R2.b)==112)?false:true;};if(_R5!=_QI){return new F(function(){return _R6(_);});}else{if(E(_R4)==1){return false;}else{return new F(function(){return _R6(_);});}}};return B(_5R(_R0,_dB));}),_R8=new T(function(){var _R9=function(_Ra){var _Rb=E(_Ra),_Rc=E(_Rb.a),_Rd=_Rc.b,_Re=E(_Rc.a),_Rf=function(_Rg){return (_Re!=_QH)?true:(E(_Rd)!=E(_QG))?true:(E(_Rb.b)==112)?false:true;};if(_Re!=_QI){return new F(function(){return _Rf(_);});}else{if(E(_Rd)==1){return false;}else{return new F(function(){return _Rf(_);});}}};return B(_5R(_R9,_dB));}),_Rh=new T(function(){var _Ri=function(_Rj){var _Rk=E(_Rj),_Rl=E(_Rk.a),_Rm=_Rl.b,_Rn=E(_Rl.a),_Ro=function(_Rp){return (_Rn!=_QH)?true:(E(_Rm)!=E(_QG))?true:(E(_Rk.b)==112)?false:true;};if(_Rn!=_QI){return new F(function(){return _Ro(_);});}else{if(E(_Rm)==1){return false;}else{return new F(function(){return _Ro(_);});}}};return B(_5R(_Ri,_dB));}),_Rq=new T(function(){var _Rr=function(_Rs){var _Rt=E(_Rs),_Ru=E(_Rt.a),_Rv=_Ru.b,_Rw=E(_Ru.a),_Rx=function(_Ry){return (_Rw!=_QH)?true:(E(_Rv)!=E(_QG))?true:(E(_Rt.b)==112)?false:true;};if(_Rw!=_QI){return new F(function(){return _Rx(_);});}else{if(E(_Rv)==1){return false;}else{return new F(function(){return _Rx(_);});}}};return B(_5R(_Rr,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,_QW,_bv),_Rq),b:_5L,c:_QY,d:_ds,e:_8U,f:_8S,g:_8L,h:_8L,i:_5K},new T2(1,{_:0,a:new T2(1,new T2(0,_QW,_95),_Rh),b:_5L,c:_QY,d:_ds,e:_8M,f:_8S,g:_8L,h:_8L,i:_5K},new T2(1,{_:0,a:new T2(1,new T2(0,_QW,_bP),_R8),b:_5L,c:_QY,d:_ds,e:_8M,f:_8S,g:_8L,h:_8L,i:_5K},new T2(1,{_:0,a:new T2(1,new T2(0,_QW,_bw),_QZ),b:_5L,c:_QY,d:_ds,e:_8M,f:_8S,g:_8L,h:_8L,i:_5K},_QE))));}else{var _Rz=new T(function(){var _RA=function(_RB){var _RC=E(_RB),_RD=E(_RC.a),_RE=_RD.b,_RF=E(_RD.a),_RG=function(_RH){return (_RF!=_QH)?true:(E(_RE)!=E(_QG))?true:(E(_RC.b)==112)?false:true;};if(_RF!=_QI){return new F(function(){return _RG(_);});}else{if(E(_RE)!=_QX){return new F(function(){return _RG(_);});}else{return false;}}};return B(_5R(_RA,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,_QW,_ch),_Rz),b:_5L,c:_dr,d:_ds,e:_8U,f:_8S,g:_8L,h:_8L,i:_5K},_QE);}}}}}}},_RI=new T(function(){return B(_QC(1,new T(function(){return B(_Qt(_Qy));})));});return new F(function(){return _QC(-1,_RI);});}else{_Qu=_Qy;return __continue;}}})(_Qu));if(_Qv!=__continue){return _Qv;}}},_RJ=function(_RK,_RL){var _RM=E(_RK),_RN=_RM.a;if(E(_RM.b)==112){var _RO=new T(function(){return E(E(_RN).b)-1|0;}),_RP=function(_RQ,_RR){var _RS=E(_RN),_RT=_RS.b,_RU=E(_RS.a),_RV=_RU+_RQ|0;if(_RV<1){return E(_RR);}else{if(_RV>8){return E(_RR);}else{var _RW=E(_RO);if(_RW<1){return E(_RR);}else{if(_RW>8){return E(_RR);}else{var _RX=function(_RY){while(1){var _RZ=E(_RY);if(!_RZ._){return false;}else{var _S0=_RZ.b,_S1=E(_RZ.a),_S2=E(_S1.a);if(E(_S2.a)!=_RV){_RY=_S0;continue;}else{if(E(_S2.b)!=_RW){_RY=_S0;continue;}else{var _S3=u_iswupper(E(_S1.b));if(!E(_S3)){_RY=_S0;continue;}else{return true;}}}}}};if(!B((function(_S4,_S5){var _S6=E(_S4),_S7=E(_S6.a);if(E(_S7.a)!=_RV){return new F(function(){return _RX(_S5);});}else{if(E(_S7.b)!=_RW){return new F(function(){return _RX(_S5);});}else{var _S8=u_iswupper(E(_S6.b));if(!E(_S8)){return new F(function(){return _RX(_S5);});}else{return true;}}}})(_dC,_dD))){return E(_RR);}else{var _S9=new T2(0,_RV,_RW),_Sa=E(_RW);if(_Sa==1){var _Sb=new T(function(){return B(_5B(0,new T(function(){if(!E(_dA)){if(E(_RV)==8){return true;}else{return false;}}else{return true;}}),B(_5B(1,new T(function(){if(!E(_dz)){if(E(_RV)==1){return true;}else{return false;}}else{return true;}}),_dr))));}),_Sc=new T(function(){var _Sd=function(_Se){var _Sf=E(_Se),_Sg=E(_Sf.a),_Sh=_Sg.b,_Si=E(_Sg.a),_Sj=function(_Sk){return (_Si!=_RU)?true:(E(_Sh)!=E(_RT))?true:(E(_Sf.b)==112)?false:true;};if(_Si!=_RV){return new F(function(){return _Sj(_);});}else{if(E(_Sh)==1){return false;}else{return new F(function(){return _Sj(_);});}}};return B(_5R(_Sd,_dB));}),_Sl=new T(function(){var _Sm=function(_Sn){var _So=E(_Sn),_Sp=E(_So.a),_Sq=_Sp.b,_Sr=E(_Sp.a),_Ss=function(_St){return (_Sr!=_RU)?true:(E(_Sq)!=E(_RT))?true:(E(_So.b)==112)?false:true;};if(_Sr!=_RV){return new F(function(){return _Ss(_);});}else{if(E(_Sq)==1){return false;}else{return new F(function(){return _Ss(_);});}}};return B(_5R(_Sm,_dB));}),_Su=new T(function(){var _Sv=function(_Sw){var _Sx=E(_Sw),_Sy=E(_Sx.a),_Sz=_Sy.b,_SA=E(_Sy.a),_SB=function(_SC){return (_SA!=_RU)?true:(E(_Sz)!=E(_RT))?true:(E(_Sx.b)==112)?false:true;};if(_SA!=_RV){return new F(function(){return _SB(_);});}else{if(E(_Sz)==1){return false;}else{return new F(function(){return _SB(_);});}}};return B(_5R(_Sv,_dB));}),_SD=new T(function(){var _SE=function(_SF){var _SG=E(_SF),_SH=E(_SG.a),_SI=_SH.b,_SJ=E(_SH.a),_SK=function(_SL){return (_SJ!=_RU)?true:(E(_SI)!=E(_RT))?true:(E(_SG.b)==112)?false:true;};if(_SJ!=_RV){return new F(function(){return _SK(_);});}else{if(E(_SI)==1){return false;}else{return new F(function(){return _SK(_);});}}};return B(_5R(_SE,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,_S9,_bv),_SD),b:_5L,c:_Sb,d:_ds,e:_8U,f:_8S,g:_8L,h:_8L,i:_5K},new T2(1,{_:0,a:new T2(1,new T2(0,_S9,_95),_Su),b:_5L,c:_Sb,d:_ds,e:_8M,f:_8S,g:_8L,h:_8L,i:_5K},new T2(1,{_:0,a:new T2(1,new T2(0,_S9,_bP),_Sl),b:_5L,c:_Sb,d:_ds,e:_8M,f:_8S,g:_8L,h:_8L,i:_5K},new T2(1,{_:0,a:new T2(1,new T2(0,_S9,_bw),_Sc),b:_5L,c:_Sb,d:_ds,e:_8M,f:_8S,g:_8L,h:_8L,i:_5K},_RR))));}else{var _SM=new T(function(){var _SN=function(_SO){var _SP=E(_SO),_SQ=E(_SP.a),_SR=_SQ.b,_SS=E(_SQ.a),_ST=function(_SU){return (_SS!=_RU)?true:(E(_SR)!=E(_RT))?true:(E(_SP.b)==112)?false:true;};if(_SS!=_RV){return new F(function(){return _ST(_);});}else{if(E(_SR)!=_Sa){return new F(function(){return _ST(_);});}else{return false;}}};return B(_5R(_SN,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,_S9,_ch),_SM),b:_5L,c:_dr,d:_ds,e:_8U,f:_8S,g:_8L,h:_8L,i:_5K},_RR);}}}}}}},_SV=new T(function(){return B(_RP(1,new T(function(){return B(_Qt(_RL));})));});return new F(function(){return _RP(-1,_SV);});}else{return new F(function(){return _Qt(_RL);});}};return B(_RJ(_dC,_dD));}),_SW=function(_SX){while(1){var _SY=B((function(_SZ){var _T0=E(_SZ);if(!_T0._){return E(_eL);}else{var _T1=_T0.b,_T2=E(_T0.a);if(E(_T2.b)==112){var _T3=E(_T2.a);if(E(_T3.b)==7){var _T4=E(E(_dC).a),_T5=_T4.b,_T6=E(_T4.a),_T7=E(_T3.a),_T8=function(_T9){if(_T6!=_T7){var _Ta=function(_Tb){var _Tc=E(_Tb);if(!_Tc._){return true;}else{var _Td=_Tc.b,_Te=E(E(_Tc.a).a),_Tf=_Te.b,_Tg=E(_Te.a),_Th=function(_Ti){if(_Tg!=_T7){return new F(function(){return _Ta(_Td);});}else{if(E(_Tf)==6){return false;}else{return new F(function(){return _Ta(_Td);});}}};if(_Tg!=_T7){return new F(function(){return _Th(_);});}else{if(E(_Tf)==5){return false;}else{return new F(function(){return _Th(_);});}}}};return new F(function(){return _Ta(_dD);});}else{if(E(_T5)==6){return false;}else{var _Tj=function(_Tk){var _Tl=E(_Tk);if(!_Tl._){return true;}else{var _Tm=_Tl.b,_Tn=E(E(_Tl.a).a),_To=_Tn.b,_Tp=E(_Tn.a),_Tq=function(_Tr){if(_Tp!=_T7){return new F(function(){return _Tj(_Tm);});}else{if(E(_To)==6){return false;}else{return new F(function(){return _Tj(_Tm);});}}};if(_Tp!=_T7){return new F(function(){return _Tq(_);});}else{if(E(_To)==5){return false;}else{return new F(function(){return _Tq(_);});}}}};return new F(function(){return _Tj(_dD);});}}},_Ts=function(_Tt){var _Tu=new T(function(){return B(_5R(function(_Tv){var _Tw=E(_Tv),_Tx=E(_Tw.a);return (E(_Tx.a)!=_T7)?true:(E(_Tx.b)==7)?(E(_Tw.b)==112)?false:true:true;},_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_T7,_8P),_ch),_Tu),b:_5L,c:_dr,d:_ds,e:_8M,f:new T2(0,_T7,_8Q),g:_8L,h:_8L,i:_5K},new T(function(){return B(_SW(_T1));}));};if(_T6!=_T7){if(!B(_T8(_))){_SX=_T1;return __continue;}else{return new F(function(){return _Ts(_);});}}else{if(E(_T5)==5){_SX=_T1;return __continue;}else{if(!B(_T8(_))){_SX=_T1;return __continue;}else{return new F(function(){return _Ts(_);});}}}}else{_SX=_T1;return __continue;}}else{_SX=_T1;return __continue;}}})(_SX));if(_SY!=__continue){return _SY;}}},_Ty=function(_Tz,_TA){var _TB=E(_Tz);if(E(_TB.b)==112){var _TC=E(_TB.a);if(E(_TC.b)==7){var _TD=E(E(_dC).a),_TE=_TD.b,_TF=E(_TD.a),_TG=E(_TC.a),_TH=function(_TI){if(_TF!=_TG){var _TJ=function(_TK){var _TL=E(_TK);if(!_TL._){return true;}else{var _TM=_TL.b,_TN=E(E(_TL.a).a),_TO=_TN.b,_TP=E(_TN.a),_TQ=function(_TR){if(_TP!=_TG){return new F(function(){return _TJ(_TM);});}else{if(E(_TO)==6){return false;}else{return new F(function(){return _TJ(_TM);});}}};if(_TP!=_TG){return new F(function(){return _TQ(_);});}else{if(E(_TO)==5){return false;}else{return new F(function(){return _TQ(_);});}}}};return new F(function(){return _TJ(_dD);});}else{if(E(_TE)==6){return false;}else{var _TS=function(_TT){var _TU=E(_TT);if(!_TU._){return true;}else{var _TV=_TU.b,_TW=E(E(_TU.a).a),_TX=_TW.b,_TY=E(_TW.a),_TZ=function(_U0){if(_TY!=_TG){return new F(function(){return _TS(_TV);});}else{if(E(_TX)==6){return false;}else{return new F(function(){return _TS(_TV);});}}};if(_TY!=_TG){return new F(function(){return _TZ(_);});}else{if(E(_TX)==5){return false;}else{return new F(function(){return _TZ(_);});}}}};return new F(function(){return _TS(_dD);});}}},_U1=function(_U2){var _U3=new T(function(){return B(_5R(function(_U4){var _U5=E(_U4),_U6=E(_U5.a);return (E(_U6.a)!=_TG)?true:(E(_U6.b)==7)?(E(_U5.b)==112)?false:true:true;},_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_TG,_8P),_ch),_U3),b:_5L,c:_dr,d:_ds,e:_8M,f:new T2(0,_TG,_8Q),g:_8L,h:_8L,i:_5K},new T(function(){return B(_SW(_TA));}));};if(_TF!=_TG){if(!B(_TH(_))){return new F(function(){return _SW(_TA);});}else{return new F(function(){return _U1(_);});}}else{if(E(_TE)==5){return new F(function(){return _SW(_TA);});}else{if(!B(_TH(_))){return new F(function(){return _SW(_TA);});}else{return new F(function(){return _U1(_);});}}}}else{return new F(function(){return _SW(_TA);});}}else{return new F(function(){return _SW(_TA);});}};return B(_Ty(_dC,_dD));}),_U7=function(_U8){while(1){var _U9=B((function(_Ua){var _Ub=E(_Ua);if(!_Ub._){return E(_eK);}else{var _Uc=_Ub.b,_Ud=E(_Ub.a),_Ue=_Ud.a;if(E(_Ud.b)==112){var _Uf=new T(function(){return E(E(_Ue).b)-1|0;}),_Ug=E(E(_dC).a),_Uh=E(_Ue),_Ui=_Uh.b,_Uj=E(_Uh.a),_Uk=function(_Ul){var _Um=E(_Uf),_Un=new T2(0,_Uj,_Um);if(E(_Um)==1){var _Uo=new T(function(){return B(_5R(function(_Up){var _Uq=E(_Up),_Ur=E(_Uq.a);return (E(_Ur.a)!=_Uj)?true:(E(_Ur.b)!=E(_Ui))?true:(E(_Uq.b)==112)?false:true;},_dB));}),_Us=new T(function(){return B(_5R(function(_Ut){var _Uu=E(_Ut),_Uv=E(_Uu.a);return (E(_Uv.a)!=_Uj)?true:(E(_Uv.b)!=E(_Ui))?true:(E(_Uu.b)==112)?false:true;},_dB));}),_Uw=new T(function(){return B(_5R(function(_Ux){var _Uy=E(_Ux),_Uz=E(_Uy.a);return (E(_Uz.a)!=_Uj)?true:(E(_Uz.b)!=E(_Ui))?true:(E(_Uy.b)==112)?false:true;},_dB));}),_UA=new T(function(){return B(_5R(function(_UB){var _UC=E(_UB),_UD=E(_UC.a);return (E(_UD.a)!=_Uj)?true:(E(_UD.b)!=E(_Ui))?true:(E(_UC.b)==112)?false:true;},_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,_Un,_bv),_UA),b:_5L,c:_dr,d:_ds,e:_8U,f:_8S,g:_8L,h:_8L,i:_5K},new T2(1,{_:0,a:new T2(1,new T2(0,_Un,_95),_Uw),b:_5L,c:_dr,d:_ds,e:_8M,f:_8S,g:_8L,h:_8L,i:_5K},new T2(1,{_:0,a:new T2(1,new T2(0,_Un,_bP),_Us),b:_5L,c:_dr,d:_ds,e:_8M,f:_8S,g:_8L,h:_8L,i:_5K},new T2(1,{_:0,a:new T2(1,new T2(0,_Un,_bw),_Uo),b:_5L,c:_dr,d:_ds,e:_8M,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_U7(_Uc));})))));}else{var _UE=new T(function(){return B(_5R(function(_UF){var _UG=E(_UF),_UH=E(_UG.a);return (E(_UH.a)!=_Uj)?true:(E(_UH.b)!=E(_Ui))?true:(E(_UG.b)==112)?false:true;},_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,_Un,_ch),_UE),b:_5L,c:_dr,d:_ds,e:_8M,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_U7(_Uc));}));}};if(E(_Ug.a)!=_Uj){var _UI=function(_UJ){while(1){var _UK=E(_UJ);if(!_UK._){return true;}else{var _UL=_UK.b,_UM=E(E(_UK.a).a);if(E(_UM.a)!=_Uj){_UJ=_UL;continue;}else{if(E(_UM.b)!=E(_Uf)){_UJ=_UL;continue;}else{return false;}}}}};if(!B(_UI(_dD))){_U8=_Uc;return __continue;}else{return new F(function(){return _Uk(_);});}}else{var _UN=E(_Uf);if(E(_Ug.b)!=_UN){var _UO=function(_UP){while(1){var _UQ=E(_UP);if(!_UQ._){return true;}else{var _UR=_UQ.b,_US=E(E(_UQ.a).a);if(E(_US.a)!=_Uj){_UP=_UR;continue;}else{if(E(_US.b)!=_UN){_UP=_UR;continue;}else{return false;}}}}};if(!B(_UO(_dD))){_U8=_Uc;return __continue;}else{return new F(function(){return _Uk(_);});}}else{_U8=_Uc;return __continue;}}}else{_U8=_Uc;return __continue;}}})(_U8));if(_U9!=__continue){return _U9;}}},_UT=function(_UU,_UV){var _UW=E(_UU),_UX=_UW.a;if(E(_UW.b)==112){var _UY=new T(function(){return E(E(_UX).b)-1|0;}),_UZ=E(E(_dC).a),_V0=E(_UX),_V1=_V0.b,_V2=E(_V0.a),_V3=function(_V4){var _V5=E(_UY),_V6=new T2(0,_V2,_V5);if(E(_V5)==1){var _V7=new T(function(){return B(_5R(function(_V8){var _V9=E(_V8),_Va=E(_V9.a);return (E(_Va.a)!=_V2)?true:(E(_Va.b)!=E(_V1))?true:(E(_V9.b)==112)?false:true;},_dB));}),_Vb=new T(function(){return B(_5R(function(_Vc){var _Vd=E(_Vc),_Ve=E(_Vd.a);return (E(_Ve.a)!=_V2)?true:(E(_Ve.b)!=E(_V1))?true:(E(_Vd.b)==112)?false:true;},_dB));}),_Vf=new T(function(){return B(_5R(function(_Vg){var _Vh=E(_Vg),_Vi=E(_Vh.a);return (E(_Vi.a)!=_V2)?true:(E(_Vi.b)!=E(_V1))?true:(E(_Vh.b)==112)?false:true;},_dB));}),_Vj=new T(function(){return B(_5R(function(_Vk){var _Vl=E(_Vk),_Vm=E(_Vl.a);return (E(_Vm.a)!=_V2)?true:(E(_Vm.b)!=E(_V1))?true:(E(_Vl.b)==112)?false:true;},_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,_V6,_bv),_Vj),b:_5L,c:_dr,d:_ds,e:_8U,f:_8S,g:_8L,h:_8L,i:_5K},new T2(1,{_:0,a:new T2(1,new T2(0,_V6,_95),_Vf),b:_5L,c:_dr,d:_ds,e:_8M,f:_8S,g:_8L,h:_8L,i:_5K},new T2(1,{_:0,a:new T2(1,new T2(0,_V6,_bP),_Vb),b:_5L,c:_dr,d:_ds,e:_8M,f:_8S,g:_8L,h:_8L,i:_5K},new T2(1,{_:0,a:new T2(1,new T2(0,_V6,_bw),_V7),b:_5L,c:_dr,d:_ds,e:_8M,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_U7(_UV));})))));}else{var _Vn=new T(function(){return B(_5R(function(_Vo){var _Vp=E(_Vo),_Vq=E(_Vp.a);return (E(_Vq.a)!=_V2)?true:(E(_Vq.b)!=E(_V1))?true:(E(_Vp.b)==112)?false:true;},_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,_V6,_ch),_Vn),b:_5L,c:_dr,d:_ds,e:_8M,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_U7(_UV));}));}};if(E(_UZ.a)!=_V2){var _Vr=function(_Vs){while(1){var _Vt=E(_Vs);if(!_Vt._){return true;}else{var _Vu=_Vt.b,_Vv=E(E(_Vt.a).a);if(E(_Vv.a)!=_V2){_Vs=_Vu;continue;}else{if(E(_Vv.b)!=E(_UY)){_Vs=_Vu;continue;}else{return false;}}}}};if(!B(_Vr(_dD))){return new F(function(){return _U7(_UV);});}else{return new F(function(){return _V3(_);});}}else{var _Vw=E(_UY);if(E(_UZ.b)!=_Vw){var _Vx=function(_Vy){while(1){var _Vz=E(_Vy);if(!_Vz._){return true;}else{var _VA=_Vz.b,_VB=E(E(_Vz.a).a);if(E(_VB.a)!=_V2){_Vy=_VA;continue;}else{if(E(_VB.b)!=_Vw){_Vy=_VA;continue;}else{return false;}}}}};if(!B(_Vx(_dD))){return new F(function(){return _U7(_UV);});}else{return new F(function(){return _V3(_);});}}else{return new F(function(){return _U7(_UV);});}}}else{return new F(function(){return _U7(_UV);});}},_VC=B(_UT(_dC,_dD));}else{var _VD=new T(function(){var _VE=new T(function(){var _VF=new T(function(){var _VG=new T(function(){var _VH=new T(function(){var _VI=new T(function(){var _VJ=new T(function(){var _VK=new T(function(){var _VL=function(_VM,_VN,_VO){var _VP=E(_dE),_VQ=E(_VP.a),_VR=E(_VQ.a),_VS=_VR+_VM|0;if(_VS<1){return E(_VO);}else{if(_VS>8){return E(_VO);}else{var _VT=E(_VQ.b),_VU=_VT+_VN|0;if(_VU<1){return E(_VO);}else{if(_VU>8){return E(_VO);}else{var _VV=function(_VW){while(1){var _VX=E(_VW);if(!_VX._){return true;}else{var _VY=_VX.b,_VZ=E(_VX.a),_W0=E(_VZ.a);if(E(_W0.a)!=_VS){_VW=_VY;continue;}else{if(E(_W0.b)!=_VU){_VW=_VY;continue;}else{var _W1=u_iswlower(E(_VZ.b));if(!E(_W1)){return false;}else{_VW=_VY;continue;}}}}}};if(!B((function(_W2,_W3){var _W4=E(_W2),_W5=E(_W4.a);if(E(_W5.a)!=_VS){return new F(function(){return _VV(_W3);});}else{if(E(_W5.b)!=_VU){return new F(function(){return _VV(_W3);});}else{var _W6=u_iswlower(E(_W4.b));if(!E(_W6)){return false;}else{return new F(function(){return _VV(_W3);});}}}})(_dC,_dD))){return E(_VO);}else{var _W7=new T(function(){var _W8=function(_W9){while(1){var _Wa=E(_W9);if(!_Wa._){return false;}else{var _Wb=_Wa.b,_Wc=E(E(_Wa.a).a);if(E(_Wc.a)!=_VS){_W9=_Wb;continue;}else{if(E(_Wc.b)!=_VU){_W9=_Wb;continue;}else{return true;}}}}};if(!B((function(_Wd,_We){var _Wf=E(E(_Wd).a);if(E(_Wf.a)!=_VS){return new F(function(){return _W8(_We);});}else{if(E(_Wf.b)!=_VU){return new F(function(){return _W8(_We);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_Wg=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_VS)==8){if(E(_VU)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_VS)==1){if(E(_VU)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_dU))));}),_Wh=new T(function(){var _Wi=function(_Wj){var _Wk=E(_Wj),_Wl=E(_Wk.a),_Wm=_Wl.b,_Wn=E(_Wl.a),_Wo=function(_Wp){return (_Wn!=_VR)?true:(E(_Wm)!=_VT)?true:(E(_Wk.b)!=E(_VP.b))?true:false;};if(_Wn!=_VS){return new F(function(){return _Wo(_);});}else{if(E(_Wm)!=_VU){return new F(function(){return _Wo(_);});}else{return false;}}};return B(_5R(_Wi,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_VS,_VU),_8X),_Wh),b:_5J,c:_Wg,d:_ds,e:_W7,f:_8S,g:_8L,h:_8L,i:_5K},_VO);}}}}}},_Wq=new T(function(){var _Wr=new T(function(){var _Ws=new T(function(){var _Wt=new T(function(){var _Wu=new T(function(){var _Wv=new T(function(){return B(_VL(-1,-1,new T(function(){return B(_VL(-1,0,_dV));})));});return B(_VL(0,-1,_Wv));});return B(_VL(1,-1,_Wu));});return B(_VL(1,0,_Wt));});return B(_VL(1,1,_Ws));});return B(_VL(0,1,_Wr));});return B(_VL(-1,1,_Wq));}),_Ww=function(_Wx){while(1){var _Wy=B((function(_Wz){var _WA=E(_Wz);if(!_WA._){return true;}else{var _WB=_WA.b,_WC=E(E(_dC).a),_WD=E(_WA.a),_WE=_WD.b,_WF=E(_WD.a);if(E(_WC.a)!=_WF){var _WG=function(_WH){while(1){var _WI=E(_WH);if(!_WI._){return true;}else{var _WJ=_WI.b,_WK=E(E(_WI.a).a);if(E(_WK.a)!=_WF){_WH=_WJ;continue;}else{if(E(_WK.b)!=E(_WE)){_WH=_WJ;continue;}else{return false;}}}}};if(!B(_WG(_dD))){return false;}else{_Wx=_WB;return __continue;}}else{var _WL=E(_WE);if(E(_WC.b)!=_WL){var _WM=function(_WN){while(1){var _WO=E(_WN);if(!_WO._){return true;}else{var _WP=_WO.b,_WQ=E(E(_WO.a).a);if(E(_WQ.a)!=_WF){_WN=_WP;continue;}else{if(E(_WQ.b)!=_WL){_WN=_WP;continue;}else{return false;}}}}};if(!B(_WM(_dD))){return false;}else{_Wx=_WB;return __continue;}}else{return false;}}}})(_Wx));if(_Wy!=__continue){return _Wy;}}},_WR=function(_WS){var _WT=E(_WS);if(!_WT._){return E(_VK);}else{var _WU=E(_WT.a),_WV=new T(function(){return B(_WR(_WT.b));});if(E(_WU.b)==81){var _WW=E(_9X);if(!_WW._){return E(_WV);}else{var _WX=_WW.b,_WY=E(_WU.a),_WZ=_WY.b,_X0=E(_WY.a),_X1=E(_WW.a),_X2=_X0+E(_X1.a)|0;if(_X2<1){var _X3=function(_X4){while(1){var _X5=B((function(_X6){var _X7=E(_X6);if(!_X7._){return E(_WV);}else{var _X8=_X7.b,_X9=E(_X7.a),_Xa=_X0+E(_X9.a)|0;if(_Xa<1){_X4=_X8;return __continue;}else{if(_Xa>8){_X4=_X8;return __continue;}else{var _Xb=E(_WZ),_Xc=_Xb+E(_X9.b)|0;if(_Xc<1){_X4=_X8;return __continue;}else{if(_Xc>8){_X4=_X8;return __continue;}else{var _Xd=B(_4i(_X0,_Xb,_Xa,_Xc));if(!_Xd._){return E(_cr);}else{var _Xe=E(_Xd.b);if(!_Xe._){return E(_8I);}else{if(!B(_Ww(B(_8D(_Xe.a,_Xe.b))))){_X4=_X8;return __continue;}else{var _Xf=function(_Xg){while(1){var _Xh=E(_Xg);if(!_Xh._){return true;}else{var _Xi=_Xh.b,_Xj=E(_Xh.a),_Xk=E(_Xj.a);if(E(_Xk.a)!=_Xa){_Xg=_Xi;continue;}else{if(E(_Xk.b)!=_Xc){_Xg=_Xi;continue;}else{var _Xl=u_iswlower(E(_Xj.b));if(!E(_Xl)){return false;}else{_Xg=_Xi;continue;}}}}}};if(!B((function(_Xm,_Xn){var _Xo=E(_Xm),_Xp=E(_Xo.a);if(E(_Xp.a)!=_Xa){return new F(function(){return _Xf(_Xn);});}else{if(E(_Xp.b)!=_Xc){return new F(function(){return _Xf(_Xn);});}else{var _Xq=u_iswlower(E(_Xo.b));if(!E(_Xq)){return false;}else{return new F(function(){return _Xf(_Xn);});}}}})(_dC,_dD))){_X4=_X8;return __continue;}else{var _Xr=new T(function(){var _Xs=function(_Xt){while(1){var _Xu=E(_Xt);if(!_Xu._){return false;}else{var _Xv=_Xu.b,_Xw=E(E(_Xu.a).a);if(E(_Xw.a)!=_Xa){_Xt=_Xv;continue;}else{if(E(_Xw.b)!=_Xc){_Xt=_Xv;continue;}else{return true;}}}}};if(!B((function(_Xx,_Xy){var _Xz=E(E(_Xx).a);if(E(_Xz.a)!=_Xa){return new F(function(){return _Xs(_Xy);});}else{if(E(_Xz.b)!=_Xc){return new F(function(){return _Xs(_Xy);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_XA=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_Xa)==8){if(E(_Xc)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_Xa)==1){if(E(_Xc)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_XB=new T(function(){var _XC=function(_XD){var _XE=E(_XD),_XF=E(_XE.a),_XG=_XF.b,_XH=E(_XF.a),_XI=function(_XJ){return (_XH!=_X0)?true:(E(_XG)!=_Xb)?true:(E(_XE.b)==81)?false:true;};if(_XH!=_Xa){return new F(function(){return _XI(_);});}else{if(E(_XG)!=_Xc){return new F(function(){return _XI(_);});}else{return false;}}};return B(_5R(_XC,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_Xa,_Xc),_9Z),_XB),b:_5J,c:_XA,d:_ds,e:_Xr,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_X3(_X8));}));}}}}}}}}}})(_X4));if(_X5!=__continue){return _X5;}}};return new F(function(){return _X3(_WX);});}else{if(_X2>8){var _XK=function(_XL){while(1){var _XM=B((function(_XN){var _XO=E(_XN);if(!_XO._){return E(_WV);}else{var _XP=_XO.b,_XQ=E(_XO.a),_XR=_X0+E(_XQ.a)|0;if(_XR<1){_XL=_XP;return __continue;}else{if(_XR>8){_XL=_XP;return __continue;}else{var _XS=E(_WZ),_XT=_XS+E(_XQ.b)|0;if(_XT<1){_XL=_XP;return __continue;}else{if(_XT>8){_XL=_XP;return __continue;}else{var _XU=B(_4i(_X0,_XS,_XR,_XT));if(!_XU._){return E(_cr);}else{var _XV=E(_XU.b);if(!_XV._){return E(_8I);}else{if(!B(_Ww(B(_8D(_XV.a,_XV.b))))){_XL=_XP;return __continue;}else{var _XW=function(_XX){while(1){var _XY=E(_XX);if(!_XY._){return true;}else{var _XZ=_XY.b,_Y0=E(_XY.a),_Y1=E(_Y0.a);if(E(_Y1.a)!=_XR){_XX=_XZ;continue;}else{if(E(_Y1.b)!=_XT){_XX=_XZ;continue;}else{var _Y2=u_iswlower(E(_Y0.b));if(!E(_Y2)){return false;}else{_XX=_XZ;continue;}}}}}};if(!B((function(_Y3,_Y4){var _Y5=E(_Y3),_Y6=E(_Y5.a);if(E(_Y6.a)!=_XR){return new F(function(){return _XW(_Y4);});}else{if(E(_Y6.b)!=_XT){return new F(function(){return _XW(_Y4);});}else{var _Y7=u_iswlower(E(_Y5.b));if(!E(_Y7)){return false;}else{return new F(function(){return _XW(_Y4);});}}}})(_dC,_dD))){_XL=_XP;return __continue;}else{var _Y8=new T(function(){var _Y9=function(_Ya){while(1){var _Yb=E(_Ya);if(!_Yb._){return false;}else{var _Yc=_Yb.b,_Yd=E(E(_Yb.a).a);if(E(_Yd.a)!=_XR){_Ya=_Yc;continue;}else{if(E(_Yd.b)!=_XT){_Ya=_Yc;continue;}else{return true;}}}}};if(!B((function(_Ye,_Yf){var _Yg=E(E(_Ye).a);if(E(_Yg.a)!=_XR){return new F(function(){return _Y9(_Yf);});}else{if(E(_Yg.b)!=_XT){return new F(function(){return _Y9(_Yf);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_Yh=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_XR)==8){if(E(_XT)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_XR)==1){if(E(_XT)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_Yi=new T(function(){var _Yj=function(_Yk){var _Yl=E(_Yk),_Ym=E(_Yl.a),_Yn=_Ym.b,_Yo=E(_Ym.a),_Yp=function(_Yq){return (_Yo!=_X0)?true:(E(_Yn)!=_XS)?true:(E(_Yl.b)==81)?false:true;};if(_Yo!=_XR){return new F(function(){return _Yp(_);});}else{if(E(_Yn)!=_XT){return new F(function(){return _Yp(_);});}else{return false;}}};return B(_5R(_Yj,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_XR,_XT),_9Z),_Yi),b:_5J,c:_Yh,d:_ds,e:_Y8,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_XK(_XP));}));}}}}}}}}}})(_XL));if(_XM!=__continue){return _XM;}}};return new F(function(){return _XK(_WX);});}else{var _Yr=E(_WZ),_Ys=_Yr+E(_X1.b)|0;if(_Ys<1){var _Yt=function(_Yu){while(1){var _Yv=B((function(_Yw){var _Yx=E(_Yw);if(!_Yx._){return E(_WV);}else{var _Yy=_Yx.b,_Yz=E(_Yx.a),_YA=_X0+E(_Yz.a)|0;if(_YA<1){_Yu=_Yy;return __continue;}else{if(_YA>8){_Yu=_Yy;return __continue;}else{var _YB=_Yr+E(_Yz.b)|0;if(_YB<1){_Yu=_Yy;return __continue;}else{if(_YB>8){_Yu=_Yy;return __continue;}else{var _YC=B(_4i(_X0,_Yr,_YA,_YB));if(!_YC._){return E(_cr);}else{var _YD=E(_YC.b);if(!_YD._){return E(_8I);}else{if(!B(_Ww(B(_8D(_YD.a,_YD.b))))){_Yu=_Yy;return __continue;}else{var _YE=function(_YF){while(1){var _YG=E(_YF);if(!_YG._){return true;}else{var _YH=_YG.b,_YI=E(_YG.a),_YJ=E(_YI.a);if(E(_YJ.a)!=_YA){_YF=_YH;continue;}else{if(E(_YJ.b)!=_YB){_YF=_YH;continue;}else{var _YK=u_iswlower(E(_YI.b));if(!E(_YK)){return false;}else{_YF=_YH;continue;}}}}}};if(!B((function(_YL,_YM){var _YN=E(_YL),_YO=E(_YN.a);if(E(_YO.a)!=_YA){return new F(function(){return _YE(_YM);});}else{if(E(_YO.b)!=_YB){return new F(function(){return _YE(_YM);});}else{var _YP=u_iswlower(E(_YN.b));if(!E(_YP)){return false;}else{return new F(function(){return _YE(_YM);});}}}})(_dC,_dD))){_Yu=_Yy;return __continue;}else{var _YQ=new T(function(){var _YR=function(_YS){while(1){var _YT=E(_YS);if(!_YT._){return false;}else{var _YU=_YT.b,_YV=E(E(_YT.a).a);if(E(_YV.a)!=_YA){_YS=_YU;continue;}else{if(E(_YV.b)!=_YB){_YS=_YU;continue;}else{return true;}}}}};if(!B((function(_YW,_YX){var _YY=E(E(_YW).a);if(E(_YY.a)!=_YA){return new F(function(){return _YR(_YX);});}else{if(E(_YY.b)!=_YB){return new F(function(){return _YR(_YX);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_YZ=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_YA)==8){if(E(_YB)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_YA)==1){if(E(_YB)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_Z0=new T(function(){var _Z1=function(_Z2){var _Z3=E(_Z2),_Z4=E(_Z3.a),_Z5=_Z4.b,_Z6=E(_Z4.a),_Z7=function(_Z8){return (_Z6!=_X0)?true:(E(_Z5)!=_Yr)?true:(E(_Z3.b)==81)?false:true;};if(_Z6!=_YA){return new F(function(){return _Z7(_);});}else{if(E(_Z5)!=_YB){return new F(function(){return _Z7(_);});}else{return false;}}};return B(_5R(_Z1,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_YA,_YB),_9Z),_Z0),b:_5J,c:_YZ,d:_ds,e:_YQ,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_Yt(_Yy));}));}}}}}}}}}})(_Yu));if(_Yv!=__continue){return _Yv;}}};return new F(function(){return _Yt(_WX);});}else{if(_Ys>8){var _Z9=function(_Za){while(1){var _Zb=B((function(_Zc){var _Zd=E(_Zc);if(!_Zd._){return E(_WV);}else{var _Ze=_Zd.b,_Zf=E(_Zd.a),_Zg=_X0+E(_Zf.a)|0;if(_Zg<1){_Za=_Ze;return __continue;}else{if(_Zg>8){_Za=_Ze;return __continue;}else{var _Zh=_Yr+E(_Zf.b)|0;if(_Zh<1){_Za=_Ze;return __continue;}else{if(_Zh>8){_Za=_Ze;return __continue;}else{var _Zi=B(_4i(_X0,_Yr,_Zg,_Zh));if(!_Zi._){return E(_cr);}else{var _Zj=E(_Zi.b);if(!_Zj._){return E(_8I);}else{if(!B(_Ww(B(_8D(_Zj.a,_Zj.b))))){_Za=_Ze;return __continue;}else{var _Zk=function(_Zl){while(1){var _Zm=E(_Zl);if(!_Zm._){return true;}else{var _Zn=_Zm.b,_Zo=E(_Zm.a),_Zp=E(_Zo.a);if(E(_Zp.a)!=_Zg){_Zl=_Zn;continue;}else{if(E(_Zp.b)!=_Zh){_Zl=_Zn;continue;}else{var _Zq=u_iswlower(E(_Zo.b));if(!E(_Zq)){return false;}else{_Zl=_Zn;continue;}}}}}};if(!B((function(_Zr,_Zs){var _Zt=E(_Zr),_Zu=E(_Zt.a);if(E(_Zu.a)!=_Zg){return new F(function(){return _Zk(_Zs);});}else{if(E(_Zu.b)!=_Zh){return new F(function(){return _Zk(_Zs);});}else{var _Zv=u_iswlower(E(_Zt.b));if(!E(_Zv)){return false;}else{return new F(function(){return _Zk(_Zs);});}}}})(_dC,_dD))){_Za=_Ze;return __continue;}else{var _Zw=new T(function(){var _Zx=function(_Zy){while(1){var _Zz=E(_Zy);if(!_Zz._){return false;}else{var _ZA=_Zz.b,_ZB=E(E(_Zz.a).a);if(E(_ZB.a)!=_Zg){_Zy=_ZA;continue;}else{if(E(_ZB.b)!=_Zh){_Zy=_ZA;continue;}else{return true;}}}}};if(!B((function(_ZC,_ZD){var _ZE=E(E(_ZC).a);if(E(_ZE.a)!=_Zg){return new F(function(){return _Zx(_ZD);});}else{if(E(_ZE.b)!=_Zh){return new F(function(){return _Zx(_ZD);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_ZF=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_Zg)==8){if(E(_Zh)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_Zg)==1){if(E(_Zh)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_ZG=new T(function(){var _ZH=function(_ZI){var _ZJ=E(_ZI),_ZK=E(_ZJ.a),_ZL=_ZK.b,_ZM=E(_ZK.a),_ZN=function(_ZO){return (_ZM!=_X0)?true:(E(_ZL)!=_Yr)?true:(E(_ZJ.b)==81)?false:true;};if(_ZM!=_Zg){return new F(function(){return _ZN(_);});}else{if(E(_ZL)!=_Zh){return new F(function(){return _ZN(_);});}else{return false;}}};return B(_5R(_ZH,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_Zg,_Zh),_9Z),_ZG),b:_5J,c:_ZF,d:_ds,e:_Zw,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_Z9(_Ze));}));}}}}}}}}}})(_Za));if(_Zb!=__continue){return _Zb;}}};return new F(function(){return _Z9(_WX);});}else{var _ZP=B(_4i(_X0,_Yr,_X2,_Ys));if(!_ZP._){return E(_cr);}else{var _ZQ=E(_ZP.b);if(!_ZQ._){return E(_8I);}else{if(!B(_Ww(B(_8D(_ZQ.a,_ZQ.b))))){var _ZR=function(_ZS){while(1){var _ZT=B((function(_ZU){var _ZV=E(_ZU);if(!_ZV._){return E(_WV);}else{var _ZW=_ZV.b,_ZX=E(_ZV.a),_ZY=_X0+E(_ZX.a)|0;if(_ZY<1){_ZS=_ZW;return __continue;}else{if(_ZY>8){_ZS=_ZW;return __continue;}else{var _ZZ=_Yr+E(_ZX.b)|0;if(_ZZ<1){_ZS=_ZW;return __continue;}else{if(_ZZ>8){_ZS=_ZW;return __continue;}else{var _100=B(_4i(_X0,_Yr,_ZY,_ZZ));if(!_100._){return E(_cr);}else{var _101=E(_100.b);if(!_101._){return E(_8I);}else{if(!B(_Ww(B(_8D(_101.a,_101.b))))){_ZS=_ZW;return __continue;}else{var _102=function(_103){while(1){var _104=E(_103);if(!_104._){return true;}else{var _105=_104.b,_106=E(_104.a),_107=E(_106.a);if(E(_107.a)!=_ZY){_103=_105;continue;}else{if(E(_107.b)!=_ZZ){_103=_105;continue;}else{var _108=u_iswlower(E(_106.b));if(!E(_108)){return false;}else{_103=_105;continue;}}}}}};if(!B((function(_109,_10a){var _10b=E(_109),_10c=E(_10b.a);if(E(_10c.a)!=_ZY){return new F(function(){return _102(_10a);});}else{if(E(_10c.b)!=_ZZ){return new F(function(){return _102(_10a);});}else{var _10d=u_iswlower(E(_10b.b));if(!E(_10d)){return false;}else{return new F(function(){return _102(_10a);});}}}})(_dC,_dD))){_ZS=_ZW;return __continue;}else{var _10e=new T(function(){var _10f=function(_10g){while(1){var _10h=E(_10g);if(!_10h._){return false;}else{var _10i=_10h.b,_10j=E(E(_10h.a).a);if(E(_10j.a)!=_ZY){_10g=_10i;continue;}else{if(E(_10j.b)!=_ZZ){_10g=_10i;continue;}else{return true;}}}}};if(!B((function(_10k,_10l){var _10m=E(E(_10k).a);if(E(_10m.a)!=_ZY){return new F(function(){return _10f(_10l);});}else{if(E(_10m.b)!=_ZZ){return new F(function(){return _10f(_10l);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_10n=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_ZY)==8){if(E(_ZZ)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_ZY)==1){if(E(_ZZ)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_10o=new T(function(){var _10p=function(_10q){var _10r=E(_10q),_10s=E(_10r.a),_10t=_10s.b,_10u=E(_10s.a),_10v=function(_10w){return (_10u!=_X0)?true:(E(_10t)!=_Yr)?true:(E(_10r.b)==81)?false:true;};if(_10u!=_ZY){return new F(function(){return _10v(_);});}else{if(E(_10t)!=_ZZ){return new F(function(){return _10v(_);});}else{return false;}}};return B(_5R(_10p,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_ZY,_ZZ),_9Z),_10o),b:_5J,c:_10n,d:_ds,e:_10e,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_ZR(_ZW));}));}}}}}}}}}})(_ZS));if(_ZT!=__continue){return _ZT;}}};return new F(function(){return _ZR(_WX);});}else{var _10x=function(_10y){while(1){var _10z=E(_10y);if(!_10z._){return true;}else{var _10A=_10z.b,_10B=E(_10z.a),_10C=E(_10B.a);if(E(_10C.a)!=_X2){_10y=_10A;continue;}else{if(E(_10C.b)!=_Ys){_10y=_10A;continue;}else{var _10D=u_iswlower(E(_10B.b));if(!E(_10D)){return false;}else{_10y=_10A;continue;}}}}}};if(!B((function(_10E,_10F){var _10G=E(_10E),_10H=E(_10G.a);if(E(_10H.a)!=_X2){return new F(function(){return _10x(_10F);});}else{if(E(_10H.b)!=_Ys){return new F(function(){return _10x(_10F);});}else{var _10I=u_iswlower(E(_10G.b));if(!E(_10I)){return false;}else{return new F(function(){return _10x(_10F);});}}}})(_dC,_dD))){var _10J=function(_10K){while(1){var _10L=B((function(_10M){var _10N=E(_10M);if(!_10N._){return E(_WV);}else{var _10O=_10N.b,_10P=E(_10N.a),_10Q=_X0+E(_10P.a)|0;if(_10Q<1){_10K=_10O;return __continue;}else{if(_10Q>8){_10K=_10O;return __continue;}else{var _10R=_Yr+E(_10P.b)|0;if(_10R<1){_10K=_10O;return __continue;}else{if(_10R>8){_10K=_10O;return __continue;}else{var _10S=B(_4i(_X0,_Yr,_10Q,_10R));if(!_10S._){return E(_cr);}else{var _10T=E(_10S.b);if(!_10T._){return E(_8I);}else{if(!B(_Ww(B(_8D(_10T.a,_10T.b))))){_10K=_10O;return __continue;}else{var _10U=function(_10V){while(1){var _10W=E(_10V);if(!_10W._){return true;}else{var _10X=_10W.b,_10Y=E(_10W.a),_10Z=E(_10Y.a);if(E(_10Z.a)!=_10Q){_10V=_10X;continue;}else{if(E(_10Z.b)!=_10R){_10V=_10X;continue;}else{var _110=u_iswlower(E(_10Y.b));if(!E(_110)){return false;}else{_10V=_10X;continue;}}}}}};if(!B((function(_111,_112){var _113=E(_111),_114=E(_113.a);if(E(_114.a)!=_10Q){return new F(function(){return _10U(_112);});}else{if(E(_114.b)!=_10R){return new F(function(){return _10U(_112);});}else{var _115=u_iswlower(E(_113.b));if(!E(_115)){return false;}else{return new F(function(){return _10U(_112);});}}}})(_dC,_dD))){_10K=_10O;return __continue;}else{var _116=new T(function(){var _117=function(_118){while(1){var _119=E(_118);if(!_119._){return false;}else{var _11a=_119.b,_11b=E(E(_119.a).a);if(E(_11b.a)!=_10Q){_118=_11a;continue;}else{if(E(_11b.b)!=_10R){_118=_11a;continue;}else{return true;}}}}};if(!B((function(_11c,_11d){var _11e=E(E(_11c).a);if(E(_11e.a)!=_10Q){return new F(function(){return _117(_11d);});}else{if(E(_11e.b)!=_10R){return new F(function(){return _117(_11d);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_11f=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_10Q)==8){if(E(_10R)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_10Q)==1){if(E(_10R)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_11g=new T(function(){var _11h=function(_11i){var _11j=E(_11i),_11k=E(_11j.a),_11l=_11k.b,_11m=E(_11k.a),_11n=function(_11o){return (_11m!=_X0)?true:(E(_11l)!=_Yr)?true:(E(_11j.b)==81)?false:true;};if(_11m!=_10Q){return new F(function(){return _11n(_);});}else{if(E(_11l)!=_10R){return new F(function(){return _11n(_);});}else{return false;}}};return B(_5R(_11h,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_10Q,_10R),_9Z),_11g),b:_5J,c:_11f,d:_ds,e:_116,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_10J(_10O));}));}}}}}}}}}})(_10K));if(_10L!=__continue){return _10L;}}};return new F(function(){return _10J(_WX);});}else{var _11p=new T(function(){var _11q=function(_11r){while(1){var _11s=B((function(_11t){var _11u=E(_11t);if(!_11u._){return E(_WV);}else{var _11v=_11u.b,_11w=E(_11u.a),_11x=_X0+E(_11w.a)|0;if(_11x<1){_11r=_11v;return __continue;}else{if(_11x>8){_11r=_11v;return __continue;}else{var _11y=_Yr+E(_11w.b)|0;if(_11y<1){_11r=_11v;return __continue;}else{if(_11y>8){_11r=_11v;return __continue;}else{var _11z=B(_4i(_X0,_Yr,_11x,_11y));if(!_11z._){return E(_cr);}else{var _11A=E(_11z.b);if(!_11A._){return E(_8I);}else{if(!B(_Ww(B(_8D(_11A.a,_11A.b))))){_11r=_11v;return __continue;}else{var _11B=function(_11C){while(1){var _11D=E(_11C);if(!_11D._){return true;}else{var _11E=_11D.b,_11F=E(_11D.a),_11G=E(_11F.a);if(E(_11G.a)!=_11x){_11C=_11E;continue;}else{if(E(_11G.b)!=_11y){_11C=_11E;continue;}else{var _11H=u_iswlower(E(_11F.b));if(!E(_11H)){return false;}else{_11C=_11E;continue;}}}}}};if(!B((function(_11I,_11J){var _11K=E(_11I),_11L=E(_11K.a);if(E(_11L.a)!=_11x){return new F(function(){return _11B(_11J);});}else{if(E(_11L.b)!=_11y){return new F(function(){return _11B(_11J);});}else{var _11M=u_iswlower(E(_11K.b));if(!E(_11M)){return false;}else{return new F(function(){return _11B(_11J);});}}}})(_dC,_dD))){_11r=_11v;return __continue;}else{var _11N=new T(function(){var _11O=function(_11P){while(1){var _11Q=E(_11P);if(!_11Q._){return false;}else{var _11R=_11Q.b,_11S=E(E(_11Q.a).a);if(E(_11S.a)!=_11x){_11P=_11R;continue;}else{if(E(_11S.b)!=_11y){_11P=_11R;continue;}else{return true;}}}}};if(!B((function(_11T,_11U){var _11V=E(E(_11T).a);if(E(_11V.a)!=_11x){return new F(function(){return _11O(_11U);});}else{if(E(_11V.b)!=_11y){return new F(function(){return _11O(_11U);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_11W=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_11x)==8){if(E(_11y)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_11x)==1){if(E(_11y)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_11X=new T(function(){var _11Y=function(_11Z){var _120=E(_11Z),_121=E(_120.a),_122=_121.b,_123=E(_121.a),_124=function(_125){return (_123!=_X0)?true:(E(_122)!=_Yr)?true:(E(_120.b)==81)?false:true;};if(_123!=_11x){return new F(function(){return _124(_);});}else{if(E(_122)!=_11y){return new F(function(){return _124(_);});}else{return false;}}};return B(_5R(_11Y,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_11x,_11y),_9Z),_11X),b:_5J,c:_11W,d:_ds,e:_11N,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_11q(_11v));}));}}}}}}}}}})(_11r));if(_11s!=__continue){return _11s;}}};return B(_11q(_WX));}),_126=new T(function(){var _127=function(_128){while(1){var _129=E(_128);if(!_129._){return false;}else{var _12a=_129.b,_12b=E(E(_129.a).a);if(E(_12b.a)!=_X2){_128=_12a;continue;}else{if(E(_12b.b)!=_Ys){_128=_12a;continue;}else{return true;}}}}};if(!B((function(_12c,_12d){var _12e=E(E(_12c).a);if(E(_12e.a)!=_X2){return new F(function(){return _127(_12d);});}else{if(E(_12e.b)!=_Ys){return new F(function(){return _127(_12d);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_12f=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_X2)==8){if(E(_Ys)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_X2)==1){if(E(_Ys)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_12g=new T(function(){var _12h=function(_12i){var _12j=E(_12i),_12k=E(_12j.a),_12l=_12k.b,_12m=E(_12k.a),_12n=function(_12o){return (_12m!=_X0)?true:(E(_12l)!=_Yr)?true:(E(_12j.b)==81)?false:true;};if(_12m!=_X2){return new F(function(){return _12n(_);});}else{if(E(_12l)!=_Ys){return new F(function(){return _12n(_);});}else{return false;}}};return B(_5R(_12h,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_X2,_Ys),_9Z),_12g),b:_5J,c:_12f,d:_ds,e:_126,f:_8S,g:_8L,h:_8L,i:_5K},_11p);}}}}}}}}}}else{return E(_WV);}}},_12p=function(_12q,_12r){var _12s=E(_12q),_12t=new T(function(){return B(_WR(_12r));});if(E(_12s.b)==81){var _12u=E(_9X);if(!_12u._){return E(_12t);}else{var _12v=_12u.b,_12w=E(_12s.a),_12x=_12w.b,_12y=E(_12w.a),_12z=E(_12u.a),_12A=_12y+E(_12z.a)|0;if(_12A<1){var _12B=function(_12C){while(1){var _12D=B((function(_12E){var _12F=E(_12E);if(!_12F._){return E(_12t);}else{var _12G=_12F.b,_12H=E(_12F.a),_12I=_12y+E(_12H.a)|0;if(_12I<1){_12C=_12G;return __continue;}else{if(_12I>8){_12C=_12G;return __continue;}else{var _12J=E(_12x),_12K=_12J+E(_12H.b)|0;if(_12K<1){_12C=_12G;return __continue;}else{if(_12K>8){_12C=_12G;return __continue;}else{var _12L=B(_4i(_12y,_12J,_12I,_12K));if(!_12L._){return E(_cr);}else{var _12M=E(_12L.b);if(!_12M._){return E(_8I);}else{if(!B(_Ww(B(_8D(_12M.a,_12M.b))))){_12C=_12G;return __continue;}else{var _12N=function(_12O){while(1){var _12P=E(_12O);if(!_12P._){return true;}else{var _12Q=_12P.b,_12R=E(_12P.a),_12S=E(_12R.a);if(E(_12S.a)!=_12I){_12O=_12Q;continue;}else{if(E(_12S.b)!=_12K){_12O=_12Q;continue;}else{var _12T=u_iswlower(E(_12R.b));if(!E(_12T)){return false;}else{_12O=_12Q;continue;}}}}}};if(!B((function(_12U,_12V){var _12W=E(_12U),_12X=E(_12W.a);if(E(_12X.a)!=_12I){return new F(function(){return _12N(_12V);});}else{if(E(_12X.b)!=_12K){return new F(function(){return _12N(_12V);});}else{var _12Y=u_iswlower(E(_12W.b));if(!E(_12Y)){return false;}else{return new F(function(){return _12N(_12V);});}}}})(_dC,_dD))){_12C=_12G;return __continue;}else{var _12Z=new T(function(){var _130=function(_131){while(1){var _132=E(_131);if(!_132._){return false;}else{var _133=_132.b,_134=E(E(_132.a).a);if(E(_134.a)!=_12I){_131=_133;continue;}else{if(E(_134.b)!=_12K){_131=_133;continue;}else{return true;}}}}};if(!B((function(_135,_136){var _137=E(E(_135).a);if(E(_137.a)!=_12I){return new F(function(){return _130(_136);});}else{if(E(_137.b)!=_12K){return new F(function(){return _130(_136);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_138=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_12I)==8){if(E(_12K)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_12I)==1){if(E(_12K)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_139=new T(function(){var _13a=function(_13b){var _13c=E(_13b),_13d=E(_13c.a),_13e=_13d.b,_13f=E(_13d.a),_13g=function(_13h){return (_13f!=_12y)?true:(E(_13e)!=_12J)?true:(E(_13c.b)==81)?false:true;};if(_13f!=_12I){return new F(function(){return _13g(_);});}else{if(E(_13e)!=_12K){return new F(function(){return _13g(_);});}else{return false;}}};return B(_5R(_13a,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_12I,_12K),_9Z),_139),b:_5J,c:_138,d:_ds,e:_12Z,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_12B(_12G));}));}}}}}}}}}})(_12C));if(_12D!=__continue){return _12D;}}};return new F(function(){return _12B(_12v);});}else{if(_12A>8){var _13i=function(_13j){while(1){var _13k=B((function(_13l){var _13m=E(_13l);if(!_13m._){return E(_12t);}else{var _13n=_13m.b,_13o=E(_13m.a),_13p=_12y+E(_13o.a)|0;if(_13p<1){_13j=_13n;return __continue;}else{if(_13p>8){_13j=_13n;return __continue;}else{var _13q=E(_12x),_13r=_13q+E(_13o.b)|0;if(_13r<1){_13j=_13n;return __continue;}else{if(_13r>8){_13j=_13n;return __continue;}else{var _13s=B(_4i(_12y,_13q,_13p,_13r));if(!_13s._){return E(_cr);}else{var _13t=E(_13s.b);if(!_13t._){return E(_8I);}else{if(!B(_Ww(B(_8D(_13t.a,_13t.b))))){_13j=_13n;return __continue;}else{var _13u=function(_13v){while(1){var _13w=E(_13v);if(!_13w._){return true;}else{var _13x=_13w.b,_13y=E(_13w.a),_13z=E(_13y.a);if(E(_13z.a)!=_13p){_13v=_13x;continue;}else{if(E(_13z.b)!=_13r){_13v=_13x;continue;}else{var _13A=u_iswlower(E(_13y.b));if(!E(_13A)){return false;}else{_13v=_13x;continue;}}}}}};if(!B((function(_13B,_13C){var _13D=E(_13B),_13E=E(_13D.a);if(E(_13E.a)!=_13p){return new F(function(){return _13u(_13C);});}else{if(E(_13E.b)!=_13r){return new F(function(){return _13u(_13C);});}else{var _13F=u_iswlower(E(_13D.b));if(!E(_13F)){return false;}else{return new F(function(){return _13u(_13C);});}}}})(_dC,_dD))){_13j=_13n;return __continue;}else{var _13G=new T(function(){var _13H=function(_13I){while(1){var _13J=E(_13I);if(!_13J._){return false;}else{var _13K=_13J.b,_13L=E(E(_13J.a).a);if(E(_13L.a)!=_13p){_13I=_13K;continue;}else{if(E(_13L.b)!=_13r){_13I=_13K;continue;}else{return true;}}}}};if(!B((function(_13M,_13N){var _13O=E(E(_13M).a);if(E(_13O.a)!=_13p){return new F(function(){return _13H(_13N);});}else{if(E(_13O.b)!=_13r){return new F(function(){return _13H(_13N);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_13P=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_13p)==8){if(E(_13r)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_13p)==1){if(E(_13r)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_13Q=new T(function(){var _13R=function(_13S){var _13T=E(_13S),_13U=E(_13T.a),_13V=_13U.b,_13W=E(_13U.a),_13X=function(_13Y){return (_13W!=_12y)?true:(E(_13V)!=_13q)?true:(E(_13T.b)==81)?false:true;};if(_13W!=_13p){return new F(function(){return _13X(_);});}else{if(E(_13V)!=_13r){return new F(function(){return _13X(_);});}else{return false;}}};return B(_5R(_13R,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_13p,_13r),_9Z),_13Q),b:_5J,c:_13P,d:_ds,e:_13G,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_13i(_13n));}));}}}}}}}}}})(_13j));if(_13k!=__continue){return _13k;}}};return new F(function(){return _13i(_12v);});}else{var _13Z=E(_12x),_140=_13Z+E(_12z.b)|0;if(_140<1){var _141=function(_142){while(1){var _143=B((function(_144){var _145=E(_144);if(!_145._){return E(_12t);}else{var _146=_145.b,_147=E(_145.a),_148=_12y+E(_147.a)|0;if(_148<1){_142=_146;return __continue;}else{if(_148>8){_142=_146;return __continue;}else{var _149=_13Z+E(_147.b)|0;if(_149<1){_142=_146;return __continue;}else{if(_149>8){_142=_146;return __continue;}else{var _14a=B(_4i(_12y,_13Z,_148,_149));if(!_14a._){return E(_cr);}else{var _14b=E(_14a.b);if(!_14b._){return E(_8I);}else{if(!B(_Ww(B(_8D(_14b.a,_14b.b))))){_142=_146;return __continue;}else{var _14c=function(_14d){while(1){var _14e=E(_14d);if(!_14e._){return true;}else{var _14f=_14e.b,_14g=E(_14e.a),_14h=E(_14g.a);if(E(_14h.a)!=_148){_14d=_14f;continue;}else{if(E(_14h.b)!=_149){_14d=_14f;continue;}else{var _14i=u_iswlower(E(_14g.b));if(!E(_14i)){return false;}else{_14d=_14f;continue;}}}}}};if(!B((function(_14j,_14k){var _14l=E(_14j),_14m=E(_14l.a);if(E(_14m.a)!=_148){return new F(function(){return _14c(_14k);});}else{if(E(_14m.b)!=_149){return new F(function(){return _14c(_14k);});}else{var _14n=u_iswlower(E(_14l.b));if(!E(_14n)){return false;}else{return new F(function(){return _14c(_14k);});}}}})(_dC,_dD))){_142=_146;return __continue;}else{var _14o=new T(function(){var _14p=function(_14q){while(1){var _14r=E(_14q);if(!_14r._){return false;}else{var _14s=_14r.b,_14t=E(E(_14r.a).a);if(E(_14t.a)!=_148){_14q=_14s;continue;}else{if(E(_14t.b)!=_149){_14q=_14s;continue;}else{return true;}}}}};if(!B((function(_14u,_14v){var _14w=E(E(_14u).a);if(E(_14w.a)!=_148){return new F(function(){return _14p(_14v);});}else{if(E(_14w.b)!=_149){return new F(function(){return _14p(_14v);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_14x=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_148)==8){if(E(_149)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_148)==1){if(E(_149)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_14y=new T(function(){var _14z=function(_14A){var _14B=E(_14A),_14C=E(_14B.a),_14D=_14C.b,_14E=E(_14C.a),_14F=function(_14G){return (_14E!=_12y)?true:(E(_14D)!=_13Z)?true:(E(_14B.b)==81)?false:true;};if(_14E!=_148){return new F(function(){return _14F(_);});}else{if(E(_14D)!=_149){return new F(function(){return _14F(_);});}else{return false;}}};return B(_5R(_14z,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_148,_149),_9Z),_14y),b:_5J,c:_14x,d:_ds,e:_14o,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_141(_146));}));}}}}}}}}}})(_142));if(_143!=__continue){return _143;}}};return new F(function(){return _141(_12v);});}else{if(_140>8){var _14H=function(_14I){while(1){var _14J=B((function(_14K){var _14L=E(_14K);if(!_14L._){return E(_12t);}else{var _14M=_14L.b,_14N=E(_14L.a),_14O=_12y+E(_14N.a)|0;if(_14O<1){_14I=_14M;return __continue;}else{if(_14O>8){_14I=_14M;return __continue;}else{var _14P=_13Z+E(_14N.b)|0;if(_14P<1){_14I=_14M;return __continue;}else{if(_14P>8){_14I=_14M;return __continue;}else{var _14Q=B(_4i(_12y,_13Z,_14O,_14P));if(!_14Q._){return E(_cr);}else{var _14R=E(_14Q.b);if(!_14R._){return E(_8I);}else{if(!B(_Ww(B(_8D(_14R.a,_14R.b))))){_14I=_14M;return __continue;}else{var _14S=function(_14T){while(1){var _14U=E(_14T);if(!_14U._){return true;}else{var _14V=_14U.b,_14W=E(_14U.a),_14X=E(_14W.a);if(E(_14X.a)!=_14O){_14T=_14V;continue;}else{if(E(_14X.b)!=_14P){_14T=_14V;continue;}else{var _14Y=u_iswlower(E(_14W.b));if(!E(_14Y)){return false;}else{_14T=_14V;continue;}}}}}};if(!B((function(_14Z,_150){var _151=E(_14Z),_152=E(_151.a);if(E(_152.a)!=_14O){return new F(function(){return _14S(_150);});}else{if(E(_152.b)!=_14P){return new F(function(){return _14S(_150);});}else{var _153=u_iswlower(E(_151.b));if(!E(_153)){return false;}else{return new F(function(){return _14S(_150);});}}}})(_dC,_dD))){_14I=_14M;return __continue;}else{var _154=new T(function(){var _155=function(_156){while(1){var _157=E(_156);if(!_157._){return false;}else{var _158=_157.b,_159=E(E(_157.a).a);if(E(_159.a)!=_14O){_156=_158;continue;}else{if(E(_159.b)!=_14P){_156=_158;continue;}else{return true;}}}}};if(!B((function(_15a,_15b){var _15c=E(E(_15a).a);if(E(_15c.a)!=_14O){return new F(function(){return _155(_15b);});}else{if(E(_15c.b)!=_14P){return new F(function(){return _155(_15b);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_15d=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_14O)==8){if(E(_14P)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_14O)==1){if(E(_14P)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_15e=new T(function(){var _15f=function(_15g){var _15h=E(_15g),_15i=E(_15h.a),_15j=_15i.b,_15k=E(_15i.a),_15l=function(_15m){return (_15k!=_12y)?true:(E(_15j)!=_13Z)?true:(E(_15h.b)==81)?false:true;};if(_15k!=_14O){return new F(function(){return _15l(_);});}else{if(E(_15j)!=_14P){return new F(function(){return _15l(_);});}else{return false;}}};return B(_5R(_15f,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_14O,_14P),_9Z),_15e),b:_5J,c:_15d,d:_ds,e:_154,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_14H(_14M));}));}}}}}}}}}})(_14I));if(_14J!=__continue){return _14J;}}};return new F(function(){return _14H(_12v);});}else{var _15n=B(_4i(_12y,_13Z,_12A,_140));if(!_15n._){return E(_cr);}else{var _15o=E(_15n.b);if(!_15o._){return E(_8I);}else{if(!B(_Ww(B(_8D(_15o.a,_15o.b))))){var _15p=function(_15q){while(1){var _15r=B((function(_15s){var _15t=E(_15s);if(!_15t._){return E(_12t);}else{var _15u=_15t.b,_15v=E(_15t.a),_15w=_12y+E(_15v.a)|0;if(_15w<1){_15q=_15u;return __continue;}else{if(_15w>8){_15q=_15u;return __continue;}else{var _15x=_13Z+E(_15v.b)|0;if(_15x<1){_15q=_15u;return __continue;}else{if(_15x>8){_15q=_15u;return __continue;}else{var _15y=B(_4i(_12y,_13Z,_15w,_15x));if(!_15y._){return E(_cr);}else{var _15z=E(_15y.b);if(!_15z._){return E(_8I);}else{if(!B(_Ww(B(_8D(_15z.a,_15z.b))))){_15q=_15u;return __continue;}else{var _15A=function(_15B){while(1){var _15C=E(_15B);if(!_15C._){return true;}else{var _15D=_15C.b,_15E=E(_15C.a),_15F=E(_15E.a);if(E(_15F.a)!=_15w){_15B=_15D;continue;}else{if(E(_15F.b)!=_15x){_15B=_15D;continue;}else{var _15G=u_iswlower(E(_15E.b));if(!E(_15G)){return false;}else{_15B=_15D;continue;}}}}}};if(!B((function(_15H,_15I){var _15J=E(_15H),_15K=E(_15J.a);if(E(_15K.a)!=_15w){return new F(function(){return _15A(_15I);});}else{if(E(_15K.b)!=_15x){return new F(function(){return _15A(_15I);});}else{var _15L=u_iswlower(E(_15J.b));if(!E(_15L)){return false;}else{return new F(function(){return _15A(_15I);});}}}})(_dC,_dD))){_15q=_15u;return __continue;}else{var _15M=new T(function(){var _15N=function(_15O){while(1){var _15P=E(_15O);if(!_15P._){return false;}else{var _15Q=_15P.b,_15R=E(E(_15P.a).a);if(E(_15R.a)!=_15w){_15O=_15Q;continue;}else{if(E(_15R.b)!=_15x){_15O=_15Q;continue;}else{return true;}}}}};if(!B((function(_15S,_15T){var _15U=E(E(_15S).a);if(E(_15U.a)!=_15w){return new F(function(){return _15N(_15T);});}else{if(E(_15U.b)!=_15x){return new F(function(){return _15N(_15T);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_15V=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_15w)==8){if(E(_15x)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_15w)==1){if(E(_15x)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_15W=new T(function(){var _15X=function(_15Y){var _15Z=E(_15Y),_160=E(_15Z.a),_161=_160.b,_162=E(_160.a),_163=function(_164){return (_162!=_12y)?true:(E(_161)!=_13Z)?true:(E(_15Z.b)==81)?false:true;};if(_162!=_15w){return new F(function(){return _163(_);});}else{if(E(_161)!=_15x){return new F(function(){return _163(_);});}else{return false;}}};return B(_5R(_15X,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_15w,_15x),_9Z),_15W),b:_5J,c:_15V,d:_ds,e:_15M,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_15p(_15u));}));}}}}}}}}}})(_15q));if(_15r!=__continue){return _15r;}}};return new F(function(){return _15p(_12v);});}else{var _165=function(_166){while(1){var _167=E(_166);if(!_167._){return true;}else{var _168=_167.b,_169=E(_167.a),_16a=E(_169.a);if(E(_16a.a)!=_12A){_166=_168;continue;}else{if(E(_16a.b)!=_140){_166=_168;continue;}else{var _16b=u_iswlower(E(_169.b));if(!E(_16b)){return false;}else{_166=_168;continue;}}}}}};if(!B((function(_16c,_16d){var _16e=E(_16c),_16f=E(_16e.a);if(E(_16f.a)!=_12A){return new F(function(){return _165(_16d);});}else{if(E(_16f.b)!=_140){return new F(function(){return _165(_16d);});}else{var _16g=u_iswlower(E(_16e.b));if(!E(_16g)){return false;}else{return new F(function(){return _165(_16d);});}}}})(_dC,_dD))){var _16h=function(_16i){while(1){var _16j=B((function(_16k){var _16l=E(_16k);if(!_16l._){return E(_12t);}else{var _16m=_16l.b,_16n=E(_16l.a),_16o=_12y+E(_16n.a)|0;if(_16o<1){_16i=_16m;return __continue;}else{if(_16o>8){_16i=_16m;return __continue;}else{var _16p=_13Z+E(_16n.b)|0;if(_16p<1){_16i=_16m;return __continue;}else{if(_16p>8){_16i=_16m;return __continue;}else{var _16q=B(_4i(_12y,_13Z,_16o,_16p));if(!_16q._){return E(_cr);}else{var _16r=E(_16q.b);if(!_16r._){return E(_8I);}else{if(!B(_Ww(B(_8D(_16r.a,_16r.b))))){_16i=_16m;return __continue;}else{var _16s=function(_16t){while(1){var _16u=E(_16t);if(!_16u._){return true;}else{var _16v=_16u.b,_16w=E(_16u.a),_16x=E(_16w.a);if(E(_16x.a)!=_16o){_16t=_16v;continue;}else{if(E(_16x.b)!=_16p){_16t=_16v;continue;}else{var _16y=u_iswlower(E(_16w.b));if(!E(_16y)){return false;}else{_16t=_16v;continue;}}}}}};if(!B((function(_16z,_16A){var _16B=E(_16z),_16C=E(_16B.a);if(E(_16C.a)!=_16o){return new F(function(){return _16s(_16A);});}else{if(E(_16C.b)!=_16p){return new F(function(){return _16s(_16A);});}else{var _16D=u_iswlower(E(_16B.b));if(!E(_16D)){return false;}else{return new F(function(){return _16s(_16A);});}}}})(_dC,_dD))){_16i=_16m;return __continue;}else{var _16E=new T(function(){var _16F=function(_16G){while(1){var _16H=E(_16G);if(!_16H._){return false;}else{var _16I=_16H.b,_16J=E(E(_16H.a).a);if(E(_16J.a)!=_16o){_16G=_16I;continue;}else{if(E(_16J.b)!=_16p){_16G=_16I;continue;}else{return true;}}}}};if(!B((function(_16K,_16L){var _16M=E(E(_16K).a);if(E(_16M.a)!=_16o){return new F(function(){return _16F(_16L);});}else{if(E(_16M.b)!=_16p){return new F(function(){return _16F(_16L);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_16N=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_16o)==8){if(E(_16p)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_16o)==1){if(E(_16p)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_16O=new T(function(){var _16P=function(_16Q){var _16R=E(_16Q),_16S=E(_16R.a),_16T=_16S.b,_16U=E(_16S.a),_16V=function(_16W){return (_16U!=_12y)?true:(E(_16T)!=_13Z)?true:(E(_16R.b)==81)?false:true;};if(_16U!=_16o){return new F(function(){return _16V(_);});}else{if(E(_16T)!=_16p){return new F(function(){return _16V(_);});}else{return false;}}};return B(_5R(_16P,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_16o,_16p),_9Z),_16O),b:_5J,c:_16N,d:_ds,e:_16E,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_16h(_16m));}));}}}}}}}}}})(_16i));if(_16j!=__continue){return _16j;}}};return new F(function(){return _16h(_12v);});}else{var _16X=new T(function(){var _16Y=function(_16Z){while(1){var _170=B((function(_171){var _172=E(_171);if(!_172._){return E(_12t);}else{var _173=_172.b,_174=E(_172.a),_175=_12y+E(_174.a)|0;if(_175<1){_16Z=_173;return __continue;}else{if(_175>8){_16Z=_173;return __continue;}else{var _176=_13Z+E(_174.b)|0;if(_176<1){_16Z=_173;return __continue;}else{if(_176>8){_16Z=_173;return __continue;}else{var _177=B(_4i(_12y,_13Z,_175,_176));if(!_177._){return E(_cr);}else{var _178=E(_177.b);if(!_178._){return E(_8I);}else{if(!B(_Ww(B(_8D(_178.a,_178.b))))){_16Z=_173;return __continue;}else{var _179=function(_17a){while(1){var _17b=E(_17a);if(!_17b._){return true;}else{var _17c=_17b.b,_17d=E(_17b.a),_17e=E(_17d.a);if(E(_17e.a)!=_175){_17a=_17c;continue;}else{if(E(_17e.b)!=_176){_17a=_17c;continue;}else{var _17f=u_iswlower(E(_17d.b));if(!E(_17f)){return false;}else{_17a=_17c;continue;}}}}}};if(!B((function(_17g,_17h){var _17i=E(_17g),_17j=E(_17i.a);if(E(_17j.a)!=_175){return new F(function(){return _179(_17h);});}else{if(E(_17j.b)!=_176){return new F(function(){return _179(_17h);});}else{var _17k=u_iswlower(E(_17i.b));if(!E(_17k)){return false;}else{return new F(function(){return _179(_17h);});}}}})(_dC,_dD))){_16Z=_173;return __continue;}else{var _17l=new T(function(){var _17m=function(_17n){while(1){var _17o=E(_17n);if(!_17o._){return false;}else{var _17p=_17o.b,_17q=E(E(_17o.a).a);if(E(_17q.a)!=_175){_17n=_17p;continue;}else{if(E(_17q.b)!=_176){_17n=_17p;continue;}else{return true;}}}}};if(!B((function(_17r,_17s){var _17t=E(E(_17r).a);if(E(_17t.a)!=_175){return new F(function(){return _17m(_17s);});}else{if(E(_17t.b)!=_176){return new F(function(){return _17m(_17s);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_17u=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_175)==8){if(E(_176)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_175)==1){if(E(_176)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_17v=new T(function(){var _17w=function(_17x){var _17y=E(_17x),_17z=E(_17y.a),_17A=_17z.b,_17B=E(_17z.a),_17C=function(_17D){return (_17B!=_12y)?true:(E(_17A)!=_13Z)?true:(E(_17y.b)==81)?false:true;};if(_17B!=_175){return new F(function(){return _17C(_);});}else{if(E(_17A)!=_176){return new F(function(){return _17C(_);});}else{return false;}}};return B(_5R(_17w,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_175,_176),_9Z),_17v),b:_5J,c:_17u,d:_ds,e:_17l,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_16Y(_173));}));}}}}}}}}}})(_16Z));if(_170!=__continue){return _170;}}};return B(_16Y(_12v));}),_17E=new T(function(){var _17F=function(_17G){while(1){var _17H=E(_17G);if(!_17H._){return false;}else{var _17I=_17H.b,_17J=E(E(_17H.a).a);if(E(_17J.a)!=_12A){_17G=_17I;continue;}else{if(E(_17J.b)!=_140){_17G=_17I;continue;}else{return true;}}}}};if(!B((function(_17K,_17L){var _17M=E(E(_17K).a);if(E(_17M.a)!=_12A){return new F(function(){return _17F(_17L);});}else{if(E(_17M.b)!=_140){return new F(function(){return _17F(_17L);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_17N=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_12A)==8){if(E(_140)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_12A)==1){if(E(_140)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_17O=new T(function(){var _17P=function(_17Q){var _17R=E(_17Q),_17S=E(_17R.a),_17T=_17S.b,_17U=E(_17S.a),_17V=function(_17W){return (_17U!=_12y)?true:(E(_17T)!=_13Z)?true:(E(_17R.b)==81)?false:true;};if(_17U!=_12A){return new F(function(){return _17V(_);});}else{if(E(_17T)!=_140){return new F(function(){return _17V(_);});}else{return false;}}};return B(_5R(_17P,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_12A,_140),_9Z),_17O),b:_5J,c:_17N,d:_ds,e:_17E,f:_8S,g:_8L,h:_8L,i:_5K},_16X);}}}}}}}}}}else{return E(_12t);}};return B(_12p(_dC,_dD));}),_17X=function(_17Y){while(1){var _17Z=B((function(_180){var _181=E(_180);if(!_181._){return E(_VJ);}else{var _182=_181.b,_183=E(_181.a);if(E(_183.b)==78){var _184=function(_185,_186,_187){var _188=E(_183.a),_189=E(_188.a),_18a=_189+_185|0;if(_18a<1){return E(_187);}else{if(_18a>8){return E(_187);}else{var _18b=E(_188.b),_18c=_18b+_186|0;if(_18c<1){return E(_187);}else{if(_18c>8){return E(_187);}else{var _18d=function(_18e){while(1){var _18f=E(_18e);if(!_18f._){return true;}else{var _18g=_18f.b,_18h=E(_18f.a),_18i=E(_18h.a);if(E(_18i.a)!=_18a){_18e=_18g;continue;}else{if(E(_18i.b)!=_18c){_18e=_18g;continue;}else{var _18j=u_iswlower(E(_18h.b));if(!E(_18j)){return false;}else{_18e=_18g;continue;}}}}}};if(!B((function(_18k,_18l){var _18m=E(_18k),_18n=E(_18m.a);if(E(_18n.a)!=_18a){return new F(function(){return _18d(_18l);});}else{if(E(_18n.b)!=_18c){return new F(function(){return _18d(_18l);});}else{var _18o=u_iswlower(E(_18m.b));if(!E(_18o)){return false;}else{return new F(function(){return _18d(_18l);});}}}})(_dC,_dD))){return E(_187);}else{var _18p=new T(function(){var _18q=function(_18r){while(1){var _18s=E(_18r);if(!_18s._){return false;}else{var _18t=_18s.b,_18u=E(E(_18s.a).a);if(E(_18u.a)!=_18a){_18r=_18t;continue;}else{if(E(_18u.b)!=_18c){_18r=_18t;continue;}else{return true;}}}}};if(!B((function(_18v,_18w){var _18x=E(E(_18v).a);if(E(_18x.a)!=_18a){return new F(function(){return _18q(_18w);});}else{if(E(_18x.b)!=_18c){return new F(function(){return _18q(_18w);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_18y=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_18a)==8){if(E(_18c)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_18a)==1){if(E(_18c)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_18z=new T(function(){var _18A=function(_18B){var _18C=E(_18B),_18D=E(_18C.a),_18E=_18D.b,_18F=E(_18D.a),_18G=function(_18H){return (_18F!=_189)?true:(E(_18E)!=_18b)?true:(E(_18C.b)==78)?false:true;};if(_18F!=_18a){return new F(function(){return _18G(_);});}else{if(E(_18E)!=_18c){return new F(function(){return _18G(_);});}else{return false;}}};return B(_5R(_18A,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_18a,_18c),_a0),_18z),b:_5J,c:_18y,d:_ds,e:_18p,f:_8S,g:_8L,h:_8L,i:_5K},_187);}}}}}},_18I=new T(function(){var _18J=new T(function(){var _18K=new T(function(){var _18L=new T(function(){var _18M=new T(function(){var _18N=new T(function(){var _18O=new T(function(){return B(_184(-2,-1,new T(function(){return B(_17X(_182));})));});return B(_184(-1,-2,_18O));});return B(_184(2,-1,_18N));});return B(_184(-1,2,_18M));});return B(_184(-2,1,_18L));});return B(_184(1,-2,_18K));});return B(_184(2,1,_18J));});return new F(function(){return _184(1,2,_18I);});}else{_17Y=_182;return __continue;}}})(_17Y));if(_17Z!=__continue){return _17Z;}}},_18P=function(_18Q,_18R){var _18S=E(_18Q);if(E(_18S.b)==78){var _18T=function(_18U,_18V,_18W){var _18X=E(_18S.a),_18Y=E(_18X.a),_18Z=_18Y+_18U|0;if(_18Z<1){return E(_18W);}else{if(_18Z>8){return E(_18W);}else{var _190=E(_18X.b),_191=_190+_18V|0;if(_191<1){return E(_18W);}else{if(_191>8){return E(_18W);}else{var _192=function(_193){while(1){var _194=E(_193);if(!_194._){return true;}else{var _195=_194.b,_196=E(_194.a),_197=E(_196.a);if(E(_197.a)!=_18Z){_193=_195;continue;}else{if(E(_197.b)!=_191){_193=_195;continue;}else{var _198=u_iswlower(E(_196.b));if(!E(_198)){return false;}else{_193=_195;continue;}}}}}};if(!B(_192(_dB))){return E(_18W);}else{var _199=new T(function(){var _19a=function(_19b){while(1){var _19c=E(_19b);if(!_19c._){return false;}else{var _19d=_19c.b,_19e=E(E(_19c.a).a);if(E(_19e.a)!=_18Z){_19b=_19d;continue;}else{if(E(_19e.b)!=_191){_19b=_19d;continue;}else{return true;}}}}};if(!B(_19a(_dB))){return E(_8M);}else{return E(_8U);}}),_19f=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_18Z)==8){if(E(_191)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_18Z)==1){if(E(_191)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_19g=new T(function(){var _19h=function(_19i){var _19j=E(_19i),_19k=E(_19j.a),_19l=_19k.b,_19m=E(_19k.a),_19n=function(_19o){return (_19m!=_18Y)?true:(E(_19l)!=_190)?true:(E(_19j.b)==78)?false:true;};if(_19m!=_18Z){return new F(function(){return _19n(_);});}else{if(E(_19l)!=_191){return new F(function(){return _19n(_);});}else{return false;}}};return B(_5R(_19h,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_18Z,_191),_a0),_19g),b:_5J,c:_19f,d:_ds,e:_199,f:_8S,g:_8L,h:_8L,i:_5K},_18W);}}}}}},_19p=new T(function(){var _19q=new T(function(){var _19r=new T(function(){var _19s=new T(function(){var _19t=new T(function(){var _19u=new T(function(){var _19v=new T(function(){return B(_18T(-2,-1,new T(function(){return B(_17X(_18R));})));});return B(_18T(-1,-2,_19v));});return B(_18T(2,-1,_19u));});return B(_18T(-1,2,_19t));});return B(_18T(-2,1,_19s));});return B(_18T(1,-2,_19r));});return B(_18T(2,1,_19q));});return new F(function(){return _18T(1,2,_19p);});}else{return new F(function(){return _17X(_18R);});}};return B(_18P(_dC,_dD));}),_19w=function(_19x){while(1){var _19y=B((function(_19z){var _19A=E(_19z);if(!_19A._){return true;}else{var _19B=_19A.b,_19C=E(E(_dC).a),_19D=E(_19A.a),_19E=_19D.b,_19F=E(_19D.a);if(E(_19C.a)!=_19F){var _19G=function(_19H){while(1){var _19I=E(_19H);if(!_19I._){return true;}else{var _19J=_19I.b,_19K=E(E(_19I.a).a);if(E(_19K.a)!=_19F){_19H=_19J;continue;}else{if(E(_19K.b)!=E(_19E)){_19H=_19J;continue;}else{return false;}}}}};if(!B(_19G(_dD))){return false;}else{_19x=_19B;return __continue;}}else{var _19L=E(_19E);if(E(_19C.b)!=_19L){var _19M=function(_19N){while(1){var _19O=E(_19N);if(!_19O._){return true;}else{var _19P=_19O.b,_19Q=E(E(_19O.a).a);if(E(_19Q.a)!=_19F){_19N=_19P;continue;}else{if(E(_19Q.b)!=_19L){_19N=_19P;continue;}else{return false;}}}}};if(!B(_19M(_dD))){return false;}else{_19x=_19B;return __continue;}}else{return false;}}}})(_19x));if(_19y!=__continue){return _19y;}}},_19R=function(_19S){var _19T=E(_19S);if(!_19T._){return E(_VI);}else{var _19U=E(_19T.a),_19V=new T(function(){return B(_19R(_19T.b));});if(E(_19U.b)==66){var _19W=E(_ah);if(!_19W._){return E(_19V);}else{var _19X=_19W.b,_19Y=E(_19U.a),_19Z=_19Y.b,_1a0=E(_19Y.a),_1a1=E(_19W.a),_1a2=_1a0+E(_1a1.a)|0;if(_1a2<1){var _1a3=function(_1a4){while(1){var _1a5=B((function(_1a6){var _1a7=E(_1a6);if(!_1a7._){return E(_19V);}else{var _1a8=_1a7.b,_1a9=E(_1a7.a),_1aa=_1a0+E(_1a9.a)|0;if(_1aa<1){_1a4=_1a8;return __continue;}else{if(_1aa>8){_1a4=_1a8;return __continue;}else{var _1ab=E(_19Z),_1ac=_1ab+E(_1a9.b)|0;if(_1ac<1){_1a4=_1a8;return __continue;}else{if(_1ac>8){_1a4=_1a8;return __continue;}else{var _1ad=B(_4i(_1a0,_1ab,_1aa,_1ac));if(!_1ad._){return E(_cr);}else{var _1ae=E(_1ad.b);if(!_1ae._){return E(_8I);}else{if(!B(_19w(B(_8D(_1ae.a,_1ae.b))))){_1a4=_1a8;return __continue;}else{var _1af=function(_1ag){while(1){var _1ah=E(_1ag);if(!_1ah._){return true;}else{var _1ai=_1ah.b,_1aj=E(_1ah.a),_1ak=E(_1aj.a);if(E(_1ak.a)!=_1aa){_1ag=_1ai;continue;}else{if(E(_1ak.b)!=_1ac){_1ag=_1ai;continue;}else{var _1al=u_iswlower(E(_1aj.b));if(!E(_1al)){return false;}else{_1ag=_1ai;continue;}}}}}};if(!B((function(_1am,_1an){var _1ao=E(_1am),_1ap=E(_1ao.a);if(E(_1ap.a)!=_1aa){return new F(function(){return _1af(_1an);});}else{if(E(_1ap.b)!=_1ac){return new F(function(){return _1af(_1an);});}else{var _1aq=u_iswlower(E(_1ao.b));if(!E(_1aq)){return false;}else{return new F(function(){return _1af(_1an);});}}}})(_dC,_dD))){_1a4=_1a8;return __continue;}else{var _1ar=new T(function(){var _1as=function(_1at){while(1){var _1au=E(_1at);if(!_1au._){return false;}else{var _1av=_1au.b,_1aw=E(E(_1au.a).a);if(E(_1aw.a)!=_1aa){_1at=_1av;continue;}else{if(E(_1aw.b)!=_1ac){_1at=_1av;continue;}else{return true;}}}}};if(!B((function(_1ax,_1ay){var _1az=E(E(_1ax).a);if(E(_1az.a)!=_1aa){return new F(function(){return _1as(_1ay);});}else{if(E(_1az.b)!=_1ac){return new F(function(){return _1as(_1ay);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_1aA=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_1aa)==8){if(E(_1ac)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_1aa)==1){if(E(_1ac)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_1aB=new T(function(){var _1aC=function(_1aD){var _1aE=E(_1aD),_1aF=E(_1aE.a),_1aG=_1aF.b,_1aH=E(_1aF.a),_1aI=function(_1aJ){return (_1aH!=_1a0)?true:(E(_1aG)!=_1ab)?true:(E(_1aE.b)==66)?false:true;};if(_1aH!=_1aa){return new F(function(){return _1aI(_);});}else{if(E(_1aG)!=_1ac){return new F(function(){return _1aI(_);});}else{return false;}}};return B(_5R(_1aC,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1aa,_1ac),_aj),_1aB),b:_5J,c:_1aA,d:_ds,e:_1ar,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_1a3(_1a8));}));}}}}}}}}}})(_1a4));if(_1a5!=__continue){return _1a5;}}};return new F(function(){return _1a3(_19X);});}else{if(_1a2>8){var _1aK=function(_1aL){while(1){var _1aM=B((function(_1aN){var _1aO=E(_1aN);if(!_1aO._){return E(_19V);}else{var _1aP=_1aO.b,_1aQ=E(_1aO.a),_1aR=_1a0+E(_1aQ.a)|0;if(_1aR<1){_1aL=_1aP;return __continue;}else{if(_1aR>8){_1aL=_1aP;return __continue;}else{var _1aS=E(_19Z),_1aT=_1aS+E(_1aQ.b)|0;if(_1aT<1){_1aL=_1aP;return __continue;}else{if(_1aT>8){_1aL=_1aP;return __continue;}else{var _1aU=B(_4i(_1a0,_1aS,_1aR,_1aT));if(!_1aU._){return E(_cr);}else{var _1aV=E(_1aU.b);if(!_1aV._){return E(_8I);}else{if(!B(_19w(B(_8D(_1aV.a,_1aV.b))))){_1aL=_1aP;return __continue;}else{var _1aW=function(_1aX){while(1){var _1aY=E(_1aX);if(!_1aY._){return true;}else{var _1aZ=_1aY.b,_1b0=E(_1aY.a),_1b1=E(_1b0.a);if(E(_1b1.a)!=_1aR){_1aX=_1aZ;continue;}else{if(E(_1b1.b)!=_1aT){_1aX=_1aZ;continue;}else{var _1b2=u_iswlower(E(_1b0.b));if(!E(_1b2)){return false;}else{_1aX=_1aZ;continue;}}}}}};if(!B((function(_1b3,_1b4){var _1b5=E(_1b3),_1b6=E(_1b5.a);if(E(_1b6.a)!=_1aR){return new F(function(){return _1aW(_1b4);});}else{if(E(_1b6.b)!=_1aT){return new F(function(){return _1aW(_1b4);});}else{var _1b7=u_iswlower(E(_1b5.b));if(!E(_1b7)){return false;}else{return new F(function(){return _1aW(_1b4);});}}}})(_dC,_dD))){_1aL=_1aP;return __continue;}else{var _1b8=new T(function(){var _1b9=function(_1ba){while(1){var _1bb=E(_1ba);if(!_1bb._){return false;}else{var _1bc=_1bb.b,_1bd=E(E(_1bb.a).a);if(E(_1bd.a)!=_1aR){_1ba=_1bc;continue;}else{if(E(_1bd.b)!=_1aT){_1ba=_1bc;continue;}else{return true;}}}}};if(!B((function(_1be,_1bf){var _1bg=E(E(_1be).a);if(E(_1bg.a)!=_1aR){return new F(function(){return _1b9(_1bf);});}else{if(E(_1bg.b)!=_1aT){return new F(function(){return _1b9(_1bf);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_1bh=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_1aR)==8){if(E(_1aT)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_1aR)==1){if(E(_1aT)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_1bi=new T(function(){var _1bj=function(_1bk){var _1bl=E(_1bk),_1bm=E(_1bl.a),_1bn=_1bm.b,_1bo=E(_1bm.a),_1bp=function(_1bq){return (_1bo!=_1a0)?true:(E(_1bn)!=_1aS)?true:(E(_1bl.b)==66)?false:true;};if(_1bo!=_1aR){return new F(function(){return _1bp(_);});}else{if(E(_1bn)!=_1aT){return new F(function(){return _1bp(_);});}else{return false;}}};return B(_5R(_1bj,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1aR,_1aT),_aj),_1bi),b:_5J,c:_1bh,d:_ds,e:_1b8,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_1aK(_1aP));}));}}}}}}}}}})(_1aL));if(_1aM!=__continue){return _1aM;}}};return new F(function(){return _1aK(_19X);});}else{var _1br=E(_19Z),_1bs=_1br+E(_1a1.b)|0;if(_1bs<1){var _1bt=function(_1bu){while(1){var _1bv=B((function(_1bw){var _1bx=E(_1bw);if(!_1bx._){return E(_19V);}else{var _1by=_1bx.b,_1bz=E(_1bx.a),_1bA=_1a0+E(_1bz.a)|0;if(_1bA<1){_1bu=_1by;return __continue;}else{if(_1bA>8){_1bu=_1by;return __continue;}else{var _1bB=_1br+E(_1bz.b)|0;if(_1bB<1){_1bu=_1by;return __continue;}else{if(_1bB>8){_1bu=_1by;return __continue;}else{var _1bC=B(_4i(_1a0,_1br,_1bA,_1bB));if(!_1bC._){return E(_cr);}else{var _1bD=E(_1bC.b);if(!_1bD._){return E(_8I);}else{if(!B(_19w(B(_8D(_1bD.a,_1bD.b))))){_1bu=_1by;return __continue;}else{var _1bE=function(_1bF){while(1){var _1bG=E(_1bF);if(!_1bG._){return true;}else{var _1bH=_1bG.b,_1bI=E(_1bG.a),_1bJ=E(_1bI.a);if(E(_1bJ.a)!=_1bA){_1bF=_1bH;continue;}else{if(E(_1bJ.b)!=_1bB){_1bF=_1bH;continue;}else{var _1bK=u_iswlower(E(_1bI.b));if(!E(_1bK)){return false;}else{_1bF=_1bH;continue;}}}}}};if(!B((function(_1bL,_1bM){var _1bN=E(_1bL),_1bO=E(_1bN.a);if(E(_1bO.a)!=_1bA){return new F(function(){return _1bE(_1bM);});}else{if(E(_1bO.b)!=_1bB){return new F(function(){return _1bE(_1bM);});}else{var _1bP=u_iswlower(E(_1bN.b));if(!E(_1bP)){return false;}else{return new F(function(){return _1bE(_1bM);});}}}})(_dC,_dD))){_1bu=_1by;return __continue;}else{var _1bQ=new T(function(){var _1bR=function(_1bS){while(1){var _1bT=E(_1bS);if(!_1bT._){return false;}else{var _1bU=_1bT.b,_1bV=E(E(_1bT.a).a);if(E(_1bV.a)!=_1bA){_1bS=_1bU;continue;}else{if(E(_1bV.b)!=_1bB){_1bS=_1bU;continue;}else{return true;}}}}};if(!B((function(_1bW,_1bX){var _1bY=E(E(_1bW).a);if(E(_1bY.a)!=_1bA){return new F(function(){return _1bR(_1bX);});}else{if(E(_1bY.b)!=_1bB){return new F(function(){return _1bR(_1bX);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_1bZ=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_1bA)==8){if(E(_1bB)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_1bA)==1){if(E(_1bB)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_1c0=new T(function(){var _1c1=function(_1c2){var _1c3=E(_1c2),_1c4=E(_1c3.a),_1c5=_1c4.b,_1c6=E(_1c4.a),_1c7=function(_1c8){return (_1c6!=_1a0)?true:(E(_1c5)!=_1br)?true:(E(_1c3.b)==66)?false:true;};if(_1c6!=_1bA){return new F(function(){return _1c7(_);});}else{if(E(_1c5)!=_1bB){return new F(function(){return _1c7(_);});}else{return false;}}};return B(_5R(_1c1,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1bA,_1bB),_aj),_1c0),b:_5J,c:_1bZ,d:_ds,e:_1bQ,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_1bt(_1by));}));}}}}}}}}}})(_1bu));if(_1bv!=__continue){return _1bv;}}};return new F(function(){return _1bt(_19X);});}else{if(_1bs>8){var _1c9=function(_1ca){while(1){var _1cb=B((function(_1cc){var _1cd=E(_1cc);if(!_1cd._){return E(_19V);}else{var _1ce=_1cd.b,_1cf=E(_1cd.a),_1cg=_1a0+E(_1cf.a)|0;if(_1cg<1){_1ca=_1ce;return __continue;}else{if(_1cg>8){_1ca=_1ce;return __continue;}else{var _1ch=_1br+E(_1cf.b)|0;if(_1ch<1){_1ca=_1ce;return __continue;}else{if(_1ch>8){_1ca=_1ce;return __continue;}else{var _1ci=B(_4i(_1a0,_1br,_1cg,_1ch));if(!_1ci._){return E(_cr);}else{var _1cj=E(_1ci.b);if(!_1cj._){return E(_8I);}else{if(!B(_19w(B(_8D(_1cj.a,_1cj.b))))){_1ca=_1ce;return __continue;}else{var _1ck=function(_1cl){while(1){var _1cm=E(_1cl);if(!_1cm._){return true;}else{var _1cn=_1cm.b,_1co=E(_1cm.a),_1cp=E(_1co.a);if(E(_1cp.a)!=_1cg){_1cl=_1cn;continue;}else{if(E(_1cp.b)!=_1ch){_1cl=_1cn;continue;}else{var _1cq=u_iswlower(E(_1co.b));if(!E(_1cq)){return false;}else{_1cl=_1cn;continue;}}}}}};if(!B((function(_1cr,_1cs){var _1ct=E(_1cr),_1cu=E(_1ct.a);if(E(_1cu.a)!=_1cg){return new F(function(){return _1ck(_1cs);});}else{if(E(_1cu.b)!=_1ch){return new F(function(){return _1ck(_1cs);});}else{var _1cv=u_iswlower(E(_1ct.b));if(!E(_1cv)){return false;}else{return new F(function(){return _1ck(_1cs);});}}}})(_dC,_dD))){_1ca=_1ce;return __continue;}else{var _1cw=new T(function(){var _1cx=function(_1cy){while(1){var _1cz=E(_1cy);if(!_1cz._){return false;}else{var _1cA=_1cz.b,_1cB=E(E(_1cz.a).a);if(E(_1cB.a)!=_1cg){_1cy=_1cA;continue;}else{if(E(_1cB.b)!=_1ch){_1cy=_1cA;continue;}else{return true;}}}}};if(!B((function(_1cC,_1cD){var _1cE=E(E(_1cC).a);if(E(_1cE.a)!=_1cg){return new F(function(){return _1cx(_1cD);});}else{if(E(_1cE.b)!=_1ch){return new F(function(){return _1cx(_1cD);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_1cF=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_1cg)==8){if(E(_1ch)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_1cg)==1){if(E(_1ch)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_1cG=new T(function(){var _1cH=function(_1cI){var _1cJ=E(_1cI),_1cK=E(_1cJ.a),_1cL=_1cK.b,_1cM=E(_1cK.a),_1cN=function(_1cO){return (_1cM!=_1a0)?true:(E(_1cL)!=_1br)?true:(E(_1cJ.b)==66)?false:true;};if(_1cM!=_1cg){return new F(function(){return _1cN(_);});}else{if(E(_1cL)!=_1ch){return new F(function(){return _1cN(_);});}else{return false;}}};return B(_5R(_1cH,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1cg,_1ch),_aj),_1cG),b:_5J,c:_1cF,d:_ds,e:_1cw,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_1c9(_1ce));}));}}}}}}}}}})(_1ca));if(_1cb!=__continue){return _1cb;}}};return new F(function(){return _1c9(_19X);});}else{var _1cP=B(_4i(_1a0,_1br,_1a2,_1bs));if(!_1cP._){return E(_cr);}else{var _1cQ=E(_1cP.b);if(!_1cQ._){return E(_8I);}else{if(!B(_19w(B(_8D(_1cQ.a,_1cQ.b))))){var _1cR=function(_1cS){while(1){var _1cT=B((function(_1cU){var _1cV=E(_1cU);if(!_1cV._){return E(_19V);}else{var _1cW=_1cV.b,_1cX=E(_1cV.a),_1cY=_1a0+E(_1cX.a)|0;if(_1cY<1){_1cS=_1cW;return __continue;}else{if(_1cY>8){_1cS=_1cW;return __continue;}else{var _1cZ=_1br+E(_1cX.b)|0;if(_1cZ<1){_1cS=_1cW;return __continue;}else{if(_1cZ>8){_1cS=_1cW;return __continue;}else{var _1d0=B(_4i(_1a0,_1br,_1cY,_1cZ));if(!_1d0._){return E(_cr);}else{var _1d1=E(_1d0.b);if(!_1d1._){return E(_8I);}else{if(!B(_19w(B(_8D(_1d1.a,_1d1.b))))){_1cS=_1cW;return __continue;}else{var _1d2=function(_1d3){while(1){var _1d4=E(_1d3);if(!_1d4._){return true;}else{var _1d5=_1d4.b,_1d6=E(_1d4.a),_1d7=E(_1d6.a);if(E(_1d7.a)!=_1cY){_1d3=_1d5;continue;}else{if(E(_1d7.b)!=_1cZ){_1d3=_1d5;continue;}else{var _1d8=u_iswlower(E(_1d6.b));if(!E(_1d8)){return false;}else{_1d3=_1d5;continue;}}}}}};if(!B((function(_1d9,_1da){var _1db=E(_1d9),_1dc=E(_1db.a);if(E(_1dc.a)!=_1cY){return new F(function(){return _1d2(_1da);});}else{if(E(_1dc.b)!=_1cZ){return new F(function(){return _1d2(_1da);});}else{var _1dd=u_iswlower(E(_1db.b));if(!E(_1dd)){return false;}else{return new F(function(){return _1d2(_1da);});}}}})(_dC,_dD))){_1cS=_1cW;return __continue;}else{var _1de=new T(function(){var _1df=function(_1dg){while(1){var _1dh=E(_1dg);if(!_1dh._){return false;}else{var _1di=_1dh.b,_1dj=E(E(_1dh.a).a);if(E(_1dj.a)!=_1cY){_1dg=_1di;continue;}else{if(E(_1dj.b)!=_1cZ){_1dg=_1di;continue;}else{return true;}}}}};if(!B((function(_1dk,_1dl){var _1dm=E(E(_1dk).a);if(E(_1dm.a)!=_1cY){return new F(function(){return _1df(_1dl);});}else{if(E(_1dm.b)!=_1cZ){return new F(function(){return _1df(_1dl);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_1dn=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_1cY)==8){if(E(_1cZ)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_1cY)==1){if(E(_1cZ)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_1do=new T(function(){var _1dp=function(_1dq){var _1dr=E(_1dq),_1ds=E(_1dr.a),_1dt=_1ds.b,_1du=E(_1ds.a),_1dv=function(_1dw){return (_1du!=_1a0)?true:(E(_1dt)!=_1br)?true:(E(_1dr.b)==66)?false:true;};if(_1du!=_1cY){return new F(function(){return _1dv(_);});}else{if(E(_1dt)!=_1cZ){return new F(function(){return _1dv(_);});}else{return false;}}};return B(_5R(_1dp,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1cY,_1cZ),_aj),_1do),b:_5J,c:_1dn,d:_ds,e:_1de,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_1cR(_1cW));}));}}}}}}}}}})(_1cS));if(_1cT!=__continue){return _1cT;}}};return new F(function(){return _1cR(_19X);});}else{var _1dx=function(_1dy){while(1){var _1dz=E(_1dy);if(!_1dz._){return true;}else{var _1dA=_1dz.b,_1dB=E(_1dz.a),_1dC=E(_1dB.a);if(E(_1dC.a)!=_1a2){_1dy=_1dA;continue;}else{if(E(_1dC.b)!=_1bs){_1dy=_1dA;continue;}else{var _1dD=u_iswlower(E(_1dB.b));if(!E(_1dD)){return false;}else{_1dy=_1dA;continue;}}}}}};if(!B((function(_1dE,_1dF){var _1dG=E(_1dE),_1dH=E(_1dG.a);if(E(_1dH.a)!=_1a2){return new F(function(){return _1dx(_1dF);});}else{if(E(_1dH.b)!=_1bs){return new F(function(){return _1dx(_1dF);});}else{var _1dI=u_iswlower(E(_1dG.b));if(!E(_1dI)){return false;}else{return new F(function(){return _1dx(_1dF);});}}}})(_dC,_dD))){var _1dJ=function(_1dK){while(1){var _1dL=B((function(_1dM){var _1dN=E(_1dM);if(!_1dN._){return E(_19V);}else{var _1dO=_1dN.b,_1dP=E(_1dN.a),_1dQ=_1a0+E(_1dP.a)|0;if(_1dQ<1){_1dK=_1dO;return __continue;}else{if(_1dQ>8){_1dK=_1dO;return __continue;}else{var _1dR=_1br+E(_1dP.b)|0;if(_1dR<1){_1dK=_1dO;return __continue;}else{if(_1dR>8){_1dK=_1dO;return __continue;}else{var _1dS=B(_4i(_1a0,_1br,_1dQ,_1dR));if(!_1dS._){return E(_cr);}else{var _1dT=E(_1dS.b);if(!_1dT._){return E(_8I);}else{if(!B(_19w(B(_8D(_1dT.a,_1dT.b))))){_1dK=_1dO;return __continue;}else{var _1dU=function(_1dV){while(1){var _1dW=E(_1dV);if(!_1dW._){return true;}else{var _1dX=_1dW.b,_1dY=E(_1dW.a),_1dZ=E(_1dY.a);if(E(_1dZ.a)!=_1dQ){_1dV=_1dX;continue;}else{if(E(_1dZ.b)!=_1dR){_1dV=_1dX;continue;}else{var _1e0=u_iswlower(E(_1dY.b));if(!E(_1e0)){return false;}else{_1dV=_1dX;continue;}}}}}};if(!B((function(_1e1,_1e2){var _1e3=E(_1e1),_1e4=E(_1e3.a);if(E(_1e4.a)!=_1dQ){return new F(function(){return _1dU(_1e2);});}else{if(E(_1e4.b)!=_1dR){return new F(function(){return _1dU(_1e2);});}else{var _1e5=u_iswlower(E(_1e3.b));if(!E(_1e5)){return false;}else{return new F(function(){return _1dU(_1e2);});}}}})(_dC,_dD))){_1dK=_1dO;return __continue;}else{var _1e6=new T(function(){var _1e7=function(_1e8){while(1){var _1e9=E(_1e8);if(!_1e9._){return false;}else{var _1ea=_1e9.b,_1eb=E(E(_1e9.a).a);if(E(_1eb.a)!=_1dQ){_1e8=_1ea;continue;}else{if(E(_1eb.b)!=_1dR){_1e8=_1ea;continue;}else{return true;}}}}};if(!B((function(_1ec,_1ed){var _1ee=E(E(_1ec).a);if(E(_1ee.a)!=_1dQ){return new F(function(){return _1e7(_1ed);});}else{if(E(_1ee.b)!=_1dR){return new F(function(){return _1e7(_1ed);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_1ef=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_1dQ)==8){if(E(_1dR)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_1dQ)==1){if(E(_1dR)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_1eg=new T(function(){var _1eh=function(_1ei){var _1ej=E(_1ei),_1ek=E(_1ej.a),_1el=_1ek.b,_1em=E(_1ek.a),_1en=function(_1eo){return (_1em!=_1a0)?true:(E(_1el)!=_1br)?true:(E(_1ej.b)==66)?false:true;};if(_1em!=_1dQ){return new F(function(){return _1en(_);});}else{if(E(_1el)!=_1dR){return new F(function(){return _1en(_);});}else{return false;}}};return B(_5R(_1eh,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1dQ,_1dR),_aj),_1eg),b:_5J,c:_1ef,d:_ds,e:_1e6,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_1dJ(_1dO));}));}}}}}}}}}})(_1dK));if(_1dL!=__continue){return _1dL;}}};return new F(function(){return _1dJ(_19X);});}else{var _1ep=new T(function(){var _1eq=function(_1er){while(1){var _1es=B((function(_1et){var _1eu=E(_1et);if(!_1eu._){return E(_19V);}else{var _1ev=_1eu.b,_1ew=E(_1eu.a),_1ex=_1a0+E(_1ew.a)|0;if(_1ex<1){_1er=_1ev;return __continue;}else{if(_1ex>8){_1er=_1ev;return __continue;}else{var _1ey=_1br+E(_1ew.b)|0;if(_1ey<1){_1er=_1ev;return __continue;}else{if(_1ey>8){_1er=_1ev;return __continue;}else{var _1ez=B(_4i(_1a0,_1br,_1ex,_1ey));if(!_1ez._){return E(_cr);}else{var _1eA=E(_1ez.b);if(!_1eA._){return E(_8I);}else{if(!B(_19w(B(_8D(_1eA.a,_1eA.b))))){_1er=_1ev;return __continue;}else{var _1eB=function(_1eC){while(1){var _1eD=E(_1eC);if(!_1eD._){return true;}else{var _1eE=_1eD.b,_1eF=E(_1eD.a),_1eG=E(_1eF.a);if(E(_1eG.a)!=_1ex){_1eC=_1eE;continue;}else{if(E(_1eG.b)!=_1ey){_1eC=_1eE;continue;}else{var _1eH=u_iswlower(E(_1eF.b));if(!E(_1eH)){return false;}else{_1eC=_1eE;continue;}}}}}};if(!B((function(_1eI,_1eJ){var _1eK=E(_1eI),_1eL=E(_1eK.a);if(E(_1eL.a)!=_1ex){return new F(function(){return _1eB(_1eJ);});}else{if(E(_1eL.b)!=_1ey){return new F(function(){return _1eB(_1eJ);});}else{var _1eM=u_iswlower(E(_1eK.b));if(!E(_1eM)){return false;}else{return new F(function(){return _1eB(_1eJ);});}}}})(_dC,_dD))){_1er=_1ev;return __continue;}else{var _1eN=new T(function(){var _1eO=function(_1eP){while(1){var _1eQ=E(_1eP);if(!_1eQ._){return false;}else{var _1eR=_1eQ.b,_1eS=E(E(_1eQ.a).a);if(E(_1eS.a)!=_1ex){_1eP=_1eR;continue;}else{if(E(_1eS.b)!=_1ey){_1eP=_1eR;continue;}else{return true;}}}}};if(!B((function(_1eT,_1eU){var _1eV=E(E(_1eT).a);if(E(_1eV.a)!=_1ex){return new F(function(){return _1eO(_1eU);});}else{if(E(_1eV.b)!=_1ey){return new F(function(){return _1eO(_1eU);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_1eW=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_1ex)==8){if(E(_1ey)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_1ex)==1){if(E(_1ey)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_1eX=new T(function(){var _1eY=function(_1eZ){var _1f0=E(_1eZ),_1f1=E(_1f0.a),_1f2=_1f1.b,_1f3=E(_1f1.a),_1f4=function(_1f5){return (_1f3!=_1a0)?true:(E(_1f2)!=_1br)?true:(E(_1f0.b)==66)?false:true;};if(_1f3!=_1ex){return new F(function(){return _1f4(_);});}else{if(E(_1f2)!=_1ey){return new F(function(){return _1f4(_);});}else{return false;}}};return B(_5R(_1eY,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1ex,_1ey),_aj),_1eX),b:_5J,c:_1eW,d:_ds,e:_1eN,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_1eq(_1ev));}));}}}}}}}}}})(_1er));if(_1es!=__continue){return _1es;}}};return B(_1eq(_19X));}),_1f6=new T(function(){var _1f7=function(_1f8){while(1){var _1f9=E(_1f8);if(!_1f9._){return false;}else{var _1fa=_1f9.b,_1fb=E(E(_1f9.a).a);if(E(_1fb.a)!=_1a2){_1f8=_1fa;continue;}else{if(E(_1fb.b)!=_1bs){_1f8=_1fa;continue;}else{return true;}}}}};if(!B((function(_1fc,_1fd){var _1fe=E(E(_1fc).a);if(E(_1fe.a)!=_1a2){return new F(function(){return _1f7(_1fd);});}else{if(E(_1fe.b)!=_1bs){return new F(function(){return _1f7(_1fd);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_1ff=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_1a2)==8){if(E(_1bs)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_1a2)==1){if(E(_1bs)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_1fg=new T(function(){var _1fh=function(_1fi){var _1fj=E(_1fi),_1fk=E(_1fj.a),_1fl=_1fk.b,_1fm=E(_1fk.a),_1fn=function(_1fo){return (_1fm!=_1a0)?true:(E(_1fl)!=_1br)?true:(E(_1fj.b)==66)?false:true;};if(_1fm!=_1a2){return new F(function(){return _1fn(_);});}else{if(E(_1fl)!=_1bs){return new F(function(){return _1fn(_);});}else{return false;}}};return B(_5R(_1fh,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1a2,_1bs),_aj),_1fg),b:_5J,c:_1ff,d:_ds,e:_1f6,f:_8S,g:_8L,h:_8L,i:_5K},_1ep);}}}}}}}}}}else{return E(_19V);}}},_1fp=function(_1fq,_1fr){var _1fs=E(_1fq),_1ft=new T(function(){return B(_19R(_1fr));});if(E(_1fs.b)==66){var _1fu=E(_ah);if(!_1fu._){return E(_1ft);}else{var _1fv=_1fu.b,_1fw=E(_1fs.a),_1fx=_1fw.b,_1fy=E(_1fw.a),_1fz=E(_1fu.a),_1fA=_1fy+E(_1fz.a)|0;if(_1fA<1){var _1fB=function(_1fC){while(1){var _1fD=B((function(_1fE){var _1fF=E(_1fE);if(!_1fF._){return E(_1ft);}else{var _1fG=_1fF.b,_1fH=E(_1fF.a),_1fI=_1fy+E(_1fH.a)|0;if(_1fI<1){_1fC=_1fG;return __continue;}else{if(_1fI>8){_1fC=_1fG;return __continue;}else{var _1fJ=E(_1fx),_1fK=_1fJ+E(_1fH.b)|0;if(_1fK<1){_1fC=_1fG;return __continue;}else{if(_1fK>8){_1fC=_1fG;return __continue;}else{var _1fL=B(_4i(_1fy,_1fJ,_1fI,_1fK));if(!_1fL._){return E(_cr);}else{var _1fM=E(_1fL.b);if(!_1fM._){return E(_8I);}else{if(!B(_19w(B(_8D(_1fM.a,_1fM.b))))){_1fC=_1fG;return __continue;}else{var _1fN=function(_1fO){while(1){var _1fP=E(_1fO);if(!_1fP._){return true;}else{var _1fQ=_1fP.b,_1fR=E(_1fP.a),_1fS=E(_1fR.a);if(E(_1fS.a)!=_1fI){_1fO=_1fQ;continue;}else{if(E(_1fS.b)!=_1fK){_1fO=_1fQ;continue;}else{var _1fT=u_iswlower(E(_1fR.b));if(!E(_1fT)){return false;}else{_1fO=_1fQ;continue;}}}}}};if(!B((function(_1fU,_1fV){var _1fW=E(_1fU),_1fX=E(_1fW.a);if(E(_1fX.a)!=_1fI){return new F(function(){return _1fN(_1fV);});}else{if(E(_1fX.b)!=_1fK){return new F(function(){return _1fN(_1fV);});}else{var _1fY=u_iswlower(E(_1fW.b));if(!E(_1fY)){return false;}else{return new F(function(){return _1fN(_1fV);});}}}})(_dC,_dD))){_1fC=_1fG;return __continue;}else{var _1fZ=new T(function(){var _1g0=function(_1g1){while(1){var _1g2=E(_1g1);if(!_1g2._){return false;}else{var _1g3=_1g2.b,_1g4=E(E(_1g2.a).a);if(E(_1g4.a)!=_1fI){_1g1=_1g3;continue;}else{if(E(_1g4.b)!=_1fK){_1g1=_1g3;continue;}else{return true;}}}}};if(!B((function(_1g5,_1g6){var _1g7=E(E(_1g5).a);if(E(_1g7.a)!=_1fI){return new F(function(){return _1g0(_1g6);});}else{if(E(_1g7.b)!=_1fK){return new F(function(){return _1g0(_1g6);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_1g8=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_1fI)==8){if(E(_1fK)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_1fI)==1){if(E(_1fK)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_1g9=new T(function(){var _1ga=function(_1gb){var _1gc=E(_1gb),_1gd=E(_1gc.a),_1ge=_1gd.b,_1gf=E(_1gd.a),_1gg=function(_1gh){return (_1gf!=_1fy)?true:(E(_1ge)!=_1fJ)?true:(E(_1gc.b)==66)?false:true;};if(_1gf!=_1fI){return new F(function(){return _1gg(_);});}else{if(E(_1ge)!=_1fK){return new F(function(){return _1gg(_);});}else{return false;}}};return B(_5R(_1ga,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1fI,_1fK),_aj),_1g9),b:_5J,c:_1g8,d:_ds,e:_1fZ,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_1fB(_1fG));}));}}}}}}}}}})(_1fC));if(_1fD!=__continue){return _1fD;}}};return new F(function(){return _1fB(_1fv);});}else{if(_1fA>8){var _1gi=function(_1gj){while(1){var _1gk=B((function(_1gl){var _1gm=E(_1gl);if(!_1gm._){return E(_1ft);}else{var _1gn=_1gm.b,_1go=E(_1gm.a),_1gp=_1fy+E(_1go.a)|0;if(_1gp<1){_1gj=_1gn;return __continue;}else{if(_1gp>8){_1gj=_1gn;return __continue;}else{var _1gq=E(_1fx),_1gr=_1gq+E(_1go.b)|0;if(_1gr<1){_1gj=_1gn;return __continue;}else{if(_1gr>8){_1gj=_1gn;return __continue;}else{var _1gs=B(_4i(_1fy,_1gq,_1gp,_1gr));if(!_1gs._){return E(_cr);}else{var _1gt=E(_1gs.b);if(!_1gt._){return E(_8I);}else{if(!B(_19w(B(_8D(_1gt.a,_1gt.b))))){_1gj=_1gn;return __continue;}else{var _1gu=function(_1gv){while(1){var _1gw=E(_1gv);if(!_1gw._){return true;}else{var _1gx=_1gw.b,_1gy=E(_1gw.a),_1gz=E(_1gy.a);if(E(_1gz.a)!=_1gp){_1gv=_1gx;continue;}else{if(E(_1gz.b)!=_1gr){_1gv=_1gx;continue;}else{var _1gA=u_iswlower(E(_1gy.b));if(!E(_1gA)){return false;}else{_1gv=_1gx;continue;}}}}}};if(!B((function(_1gB,_1gC){var _1gD=E(_1gB),_1gE=E(_1gD.a);if(E(_1gE.a)!=_1gp){return new F(function(){return _1gu(_1gC);});}else{if(E(_1gE.b)!=_1gr){return new F(function(){return _1gu(_1gC);});}else{var _1gF=u_iswlower(E(_1gD.b));if(!E(_1gF)){return false;}else{return new F(function(){return _1gu(_1gC);});}}}})(_dC,_dD))){_1gj=_1gn;return __continue;}else{var _1gG=new T(function(){var _1gH=function(_1gI){while(1){var _1gJ=E(_1gI);if(!_1gJ._){return false;}else{var _1gK=_1gJ.b,_1gL=E(E(_1gJ.a).a);if(E(_1gL.a)!=_1gp){_1gI=_1gK;continue;}else{if(E(_1gL.b)!=_1gr){_1gI=_1gK;continue;}else{return true;}}}}};if(!B((function(_1gM,_1gN){var _1gO=E(E(_1gM).a);if(E(_1gO.a)!=_1gp){return new F(function(){return _1gH(_1gN);});}else{if(E(_1gO.b)!=_1gr){return new F(function(){return _1gH(_1gN);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_1gP=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_1gp)==8){if(E(_1gr)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_1gp)==1){if(E(_1gr)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_1gQ=new T(function(){var _1gR=function(_1gS){var _1gT=E(_1gS),_1gU=E(_1gT.a),_1gV=_1gU.b,_1gW=E(_1gU.a),_1gX=function(_1gY){return (_1gW!=_1fy)?true:(E(_1gV)!=_1gq)?true:(E(_1gT.b)==66)?false:true;};if(_1gW!=_1gp){return new F(function(){return _1gX(_);});}else{if(E(_1gV)!=_1gr){return new F(function(){return _1gX(_);});}else{return false;}}};return B(_5R(_1gR,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1gp,_1gr),_aj),_1gQ),b:_5J,c:_1gP,d:_ds,e:_1gG,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_1gi(_1gn));}));}}}}}}}}}})(_1gj));if(_1gk!=__continue){return _1gk;}}};return new F(function(){return _1gi(_1fv);});}else{var _1gZ=E(_1fx),_1h0=_1gZ+E(_1fz.b)|0;if(_1h0<1){var _1h1=function(_1h2){while(1){var _1h3=B((function(_1h4){var _1h5=E(_1h4);if(!_1h5._){return E(_1ft);}else{var _1h6=_1h5.b,_1h7=E(_1h5.a),_1h8=_1fy+E(_1h7.a)|0;if(_1h8<1){_1h2=_1h6;return __continue;}else{if(_1h8>8){_1h2=_1h6;return __continue;}else{var _1h9=_1gZ+E(_1h7.b)|0;if(_1h9<1){_1h2=_1h6;return __continue;}else{if(_1h9>8){_1h2=_1h6;return __continue;}else{var _1ha=B(_4i(_1fy,_1gZ,_1h8,_1h9));if(!_1ha._){return E(_cr);}else{var _1hb=E(_1ha.b);if(!_1hb._){return E(_8I);}else{if(!B(_19w(B(_8D(_1hb.a,_1hb.b))))){_1h2=_1h6;return __continue;}else{var _1hc=function(_1hd){while(1){var _1he=E(_1hd);if(!_1he._){return true;}else{var _1hf=_1he.b,_1hg=E(_1he.a),_1hh=E(_1hg.a);if(E(_1hh.a)!=_1h8){_1hd=_1hf;continue;}else{if(E(_1hh.b)!=_1h9){_1hd=_1hf;continue;}else{var _1hi=u_iswlower(E(_1hg.b));if(!E(_1hi)){return false;}else{_1hd=_1hf;continue;}}}}}};if(!B((function(_1hj,_1hk){var _1hl=E(_1hj),_1hm=E(_1hl.a);if(E(_1hm.a)!=_1h8){return new F(function(){return _1hc(_1hk);});}else{if(E(_1hm.b)!=_1h9){return new F(function(){return _1hc(_1hk);});}else{var _1hn=u_iswlower(E(_1hl.b));if(!E(_1hn)){return false;}else{return new F(function(){return _1hc(_1hk);});}}}})(_dC,_dD))){_1h2=_1h6;return __continue;}else{var _1ho=new T(function(){var _1hp=function(_1hq){while(1){var _1hr=E(_1hq);if(!_1hr._){return false;}else{var _1hs=_1hr.b,_1ht=E(E(_1hr.a).a);if(E(_1ht.a)!=_1h8){_1hq=_1hs;continue;}else{if(E(_1ht.b)!=_1h9){_1hq=_1hs;continue;}else{return true;}}}}};if(!B((function(_1hu,_1hv){var _1hw=E(E(_1hu).a);if(E(_1hw.a)!=_1h8){return new F(function(){return _1hp(_1hv);});}else{if(E(_1hw.b)!=_1h9){return new F(function(){return _1hp(_1hv);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_1hx=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_1h8)==8){if(E(_1h9)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_1h8)==1){if(E(_1h9)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_1hy=new T(function(){var _1hz=function(_1hA){var _1hB=E(_1hA),_1hC=E(_1hB.a),_1hD=_1hC.b,_1hE=E(_1hC.a),_1hF=function(_1hG){return (_1hE!=_1fy)?true:(E(_1hD)!=_1gZ)?true:(E(_1hB.b)==66)?false:true;};if(_1hE!=_1h8){return new F(function(){return _1hF(_);});}else{if(E(_1hD)!=_1h9){return new F(function(){return _1hF(_);});}else{return false;}}};return B(_5R(_1hz,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1h8,_1h9),_aj),_1hy),b:_5J,c:_1hx,d:_ds,e:_1ho,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_1h1(_1h6));}));}}}}}}}}}})(_1h2));if(_1h3!=__continue){return _1h3;}}};return new F(function(){return _1h1(_1fv);});}else{if(_1h0>8){var _1hH=function(_1hI){while(1){var _1hJ=B((function(_1hK){var _1hL=E(_1hK);if(!_1hL._){return E(_1ft);}else{var _1hM=_1hL.b,_1hN=E(_1hL.a),_1hO=_1fy+E(_1hN.a)|0;if(_1hO<1){_1hI=_1hM;return __continue;}else{if(_1hO>8){_1hI=_1hM;return __continue;}else{var _1hP=_1gZ+E(_1hN.b)|0;if(_1hP<1){_1hI=_1hM;return __continue;}else{if(_1hP>8){_1hI=_1hM;return __continue;}else{var _1hQ=B(_4i(_1fy,_1gZ,_1hO,_1hP));if(!_1hQ._){return E(_cr);}else{var _1hR=E(_1hQ.b);if(!_1hR._){return E(_8I);}else{if(!B(_19w(B(_8D(_1hR.a,_1hR.b))))){_1hI=_1hM;return __continue;}else{var _1hS=function(_1hT){while(1){var _1hU=E(_1hT);if(!_1hU._){return true;}else{var _1hV=_1hU.b,_1hW=E(_1hU.a),_1hX=E(_1hW.a);if(E(_1hX.a)!=_1hO){_1hT=_1hV;continue;}else{if(E(_1hX.b)!=_1hP){_1hT=_1hV;continue;}else{var _1hY=u_iswlower(E(_1hW.b));if(!E(_1hY)){return false;}else{_1hT=_1hV;continue;}}}}}};if(!B((function(_1hZ,_1i0){var _1i1=E(_1hZ),_1i2=E(_1i1.a);if(E(_1i2.a)!=_1hO){return new F(function(){return _1hS(_1i0);});}else{if(E(_1i2.b)!=_1hP){return new F(function(){return _1hS(_1i0);});}else{var _1i3=u_iswlower(E(_1i1.b));if(!E(_1i3)){return false;}else{return new F(function(){return _1hS(_1i0);});}}}})(_dC,_dD))){_1hI=_1hM;return __continue;}else{var _1i4=new T(function(){var _1i5=function(_1i6){while(1){var _1i7=E(_1i6);if(!_1i7._){return false;}else{var _1i8=_1i7.b,_1i9=E(E(_1i7.a).a);if(E(_1i9.a)!=_1hO){_1i6=_1i8;continue;}else{if(E(_1i9.b)!=_1hP){_1i6=_1i8;continue;}else{return true;}}}}};if(!B((function(_1ia,_1ib){var _1ic=E(E(_1ia).a);if(E(_1ic.a)!=_1hO){return new F(function(){return _1i5(_1ib);});}else{if(E(_1ic.b)!=_1hP){return new F(function(){return _1i5(_1ib);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_1id=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_1hO)==8){if(E(_1hP)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_1hO)==1){if(E(_1hP)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_1ie=new T(function(){var _1if=function(_1ig){var _1ih=E(_1ig),_1ii=E(_1ih.a),_1ij=_1ii.b,_1ik=E(_1ii.a),_1il=function(_1im){return (_1ik!=_1fy)?true:(E(_1ij)!=_1gZ)?true:(E(_1ih.b)==66)?false:true;};if(_1ik!=_1hO){return new F(function(){return _1il(_);});}else{if(E(_1ij)!=_1hP){return new F(function(){return _1il(_);});}else{return false;}}};return B(_5R(_1if,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1hO,_1hP),_aj),_1ie),b:_5J,c:_1id,d:_ds,e:_1i4,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_1hH(_1hM));}));}}}}}}}}}})(_1hI));if(_1hJ!=__continue){return _1hJ;}}};return new F(function(){return _1hH(_1fv);});}else{var _1in=B(_4i(_1fy,_1gZ,_1fA,_1h0));if(!_1in._){return E(_cr);}else{var _1io=E(_1in.b);if(!_1io._){return E(_8I);}else{if(!B(_19w(B(_8D(_1io.a,_1io.b))))){var _1ip=function(_1iq){while(1){var _1ir=B((function(_1is){var _1it=E(_1is);if(!_1it._){return E(_1ft);}else{var _1iu=_1it.b,_1iv=E(_1it.a),_1iw=_1fy+E(_1iv.a)|0;if(_1iw<1){_1iq=_1iu;return __continue;}else{if(_1iw>8){_1iq=_1iu;return __continue;}else{var _1ix=_1gZ+E(_1iv.b)|0;if(_1ix<1){_1iq=_1iu;return __continue;}else{if(_1ix>8){_1iq=_1iu;return __continue;}else{var _1iy=B(_4i(_1fy,_1gZ,_1iw,_1ix));if(!_1iy._){return E(_cr);}else{var _1iz=E(_1iy.b);if(!_1iz._){return E(_8I);}else{if(!B(_19w(B(_8D(_1iz.a,_1iz.b))))){_1iq=_1iu;return __continue;}else{var _1iA=function(_1iB){while(1){var _1iC=E(_1iB);if(!_1iC._){return true;}else{var _1iD=_1iC.b,_1iE=E(_1iC.a),_1iF=E(_1iE.a);if(E(_1iF.a)!=_1iw){_1iB=_1iD;continue;}else{if(E(_1iF.b)!=_1ix){_1iB=_1iD;continue;}else{var _1iG=u_iswlower(E(_1iE.b));if(!E(_1iG)){return false;}else{_1iB=_1iD;continue;}}}}}};if(!B((function(_1iH,_1iI){var _1iJ=E(_1iH),_1iK=E(_1iJ.a);if(E(_1iK.a)!=_1iw){return new F(function(){return _1iA(_1iI);});}else{if(E(_1iK.b)!=_1ix){return new F(function(){return _1iA(_1iI);});}else{var _1iL=u_iswlower(E(_1iJ.b));if(!E(_1iL)){return false;}else{return new F(function(){return _1iA(_1iI);});}}}})(_dC,_dD))){_1iq=_1iu;return __continue;}else{var _1iM=new T(function(){var _1iN=function(_1iO){while(1){var _1iP=E(_1iO);if(!_1iP._){return false;}else{var _1iQ=_1iP.b,_1iR=E(E(_1iP.a).a);if(E(_1iR.a)!=_1iw){_1iO=_1iQ;continue;}else{if(E(_1iR.b)!=_1ix){_1iO=_1iQ;continue;}else{return true;}}}}};if(!B((function(_1iS,_1iT){var _1iU=E(E(_1iS).a);if(E(_1iU.a)!=_1iw){return new F(function(){return _1iN(_1iT);});}else{if(E(_1iU.b)!=_1ix){return new F(function(){return _1iN(_1iT);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_1iV=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_1iw)==8){if(E(_1ix)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_1iw)==1){if(E(_1ix)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_1iW=new T(function(){var _1iX=function(_1iY){var _1iZ=E(_1iY),_1j0=E(_1iZ.a),_1j1=_1j0.b,_1j2=E(_1j0.a),_1j3=function(_1j4){return (_1j2!=_1fy)?true:(E(_1j1)!=_1gZ)?true:(E(_1iZ.b)==66)?false:true;};if(_1j2!=_1iw){return new F(function(){return _1j3(_);});}else{if(E(_1j1)!=_1ix){return new F(function(){return _1j3(_);});}else{return false;}}};return B(_5R(_1iX,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1iw,_1ix),_aj),_1iW),b:_5J,c:_1iV,d:_ds,e:_1iM,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_1ip(_1iu));}));}}}}}}}}}})(_1iq));if(_1ir!=__continue){return _1ir;}}};return new F(function(){return _1ip(_1fv);});}else{var _1j5=function(_1j6){while(1){var _1j7=E(_1j6);if(!_1j7._){return true;}else{var _1j8=_1j7.b,_1j9=E(_1j7.a),_1ja=E(_1j9.a);if(E(_1ja.a)!=_1fA){_1j6=_1j8;continue;}else{if(E(_1ja.b)!=_1h0){_1j6=_1j8;continue;}else{var _1jb=u_iswlower(E(_1j9.b));if(!E(_1jb)){return false;}else{_1j6=_1j8;continue;}}}}}};if(!B((function(_1jc,_1jd){var _1je=E(_1jc),_1jf=E(_1je.a);if(E(_1jf.a)!=_1fA){return new F(function(){return _1j5(_1jd);});}else{if(E(_1jf.b)!=_1h0){return new F(function(){return _1j5(_1jd);});}else{var _1jg=u_iswlower(E(_1je.b));if(!E(_1jg)){return false;}else{return new F(function(){return _1j5(_1jd);});}}}})(_dC,_dD))){var _1jh=function(_1ji){while(1){var _1jj=B((function(_1jk){var _1jl=E(_1jk);if(!_1jl._){return E(_1ft);}else{var _1jm=_1jl.b,_1jn=E(_1jl.a),_1jo=_1fy+E(_1jn.a)|0;if(_1jo<1){_1ji=_1jm;return __continue;}else{if(_1jo>8){_1ji=_1jm;return __continue;}else{var _1jp=_1gZ+E(_1jn.b)|0;if(_1jp<1){_1ji=_1jm;return __continue;}else{if(_1jp>8){_1ji=_1jm;return __continue;}else{var _1jq=B(_4i(_1fy,_1gZ,_1jo,_1jp));if(!_1jq._){return E(_cr);}else{var _1jr=E(_1jq.b);if(!_1jr._){return E(_8I);}else{if(!B(_19w(B(_8D(_1jr.a,_1jr.b))))){_1ji=_1jm;return __continue;}else{var _1js=function(_1jt){while(1){var _1ju=E(_1jt);if(!_1ju._){return true;}else{var _1jv=_1ju.b,_1jw=E(_1ju.a),_1jx=E(_1jw.a);if(E(_1jx.a)!=_1jo){_1jt=_1jv;continue;}else{if(E(_1jx.b)!=_1jp){_1jt=_1jv;continue;}else{var _1jy=u_iswlower(E(_1jw.b));if(!E(_1jy)){return false;}else{_1jt=_1jv;continue;}}}}}};if(!B((function(_1jz,_1jA){var _1jB=E(_1jz),_1jC=E(_1jB.a);if(E(_1jC.a)!=_1jo){return new F(function(){return _1js(_1jA);});}else{if(E(_1jC.b)!=_1jp){return new F(function(){return _1js(_1jA);});}else{var _1jD=u_iswlower(E(_1jB.b));if(!E(_1jD)){return false;}else{return new F(function(){return _1js(_1jA);});}}}})(_dC,_dD))){_1ji=_1jm;return __continue;}else{var _1jE=new T(function(){var _1jF=function(_1jG){while(1){var _1jH=E(_1jG);if(!_1jH._){return false;}else{var _1jI=_1jH.b,_1jJ=E(E(_1jH.a).a);if(E(_1jJ.a)!=_1jo){_1jG=_1jI;continue;}else{if(E(_1jJ.b)!=_1jp){_1jG=_1jI;continue;}else{return true;}}}}};if(!B((function(_1jK,_1jL){var _1jM=E(E(_1jK).a);if(E(_1jM.a)!=_1jo){return new F(function(){return _1jF(_1jL);});}else{if(E(_1jM.b)!=_1jp){return new F(function(){return _1jF(_1jL);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_1jN=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_1jo)==8){if(E(_1jp)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_1jo)==1){if(E(_1jp)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_1jO=new T(function(){var _1jP=function(_1jQ){var _1jR=E(_1jQ),_1jS=E(_1jR.a),_1jT=_1jS.b,_1jU=E(_1jS.a),_1jV=function(_1jW){return (_1jU!=_1fy)?true:(E(_1jT)!=_1gZ)?true:(E(_1jR.b)==66)?false:true;};if(_1jU!=_1jo){return new F(function(){return _1jV(_);});}else{if(E(_1jT)!=_1jp){return new F(function(){return _1jV(_);});}else{return false;}}};return B(_5R(_1jP,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1jo,_1jp),_aj),_1jO),b:_5J,c:_1jN,d:_ds,e:_1jE,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_1jh(_1jm));}));}}}}}}}}}})(_1ji));if(_1jj!=__continue){return _1jj;}}};return new F(function(){return _1jh(_1fv);});}else{var _1jX=new T(function(){var _1jY=function(_1jZ){while(1){var _1k0=B((function(_1k1){var _1k2=E(_1k1);if(!_1k2._){return E(_1ft);}else{var _1k3=_1k2.b,_1k4=E(_1k2.a),_1k5=_1fy+E(_1k4.a)|0;if(_1k5<1){_1jZ=_1k3;return __continue;}else{if(_1k5>8){_1jZ=_1k3;return __continue;}else{var _1k6=_1gZ+E(_1k4.b)|0;if(_1k6<1){_1jZ=_1k3;return __continue;}else{if(_1k6>8){_1jZ=_1k3;return __continue;}else{var _1k7=B(_4i(_1fy,_1gZ,_1k5,_1k6));if(!_1k7._){return E(_cr);}else{var _1k8=E(_1k7.b);if(!_1k8._){return E(_8I);}else{if(!B(_19w(B(_8D(_1k8.a,_1k8.b))))){_1jZ=_1k3;return __continue;}else{var _1k9=function(_1ka){while(1){var _1kb=E(_1ka);if(!_1kb._){return true;}else{var _1kc=_1kb.b,_1kd=E(_1kb.a),_1ke=E(_1kd.a);if(E(_1ke.a)!=_1k5){_1ka=_1kc;continue;}else{if(E(_1ke.b)!=_1k6){_1ka=_1kc;continue;}else{var _1kf=u_iswlower(E(_1kd.b));if(!E(_1kf)){return false;}else{_1ka=_1kc;continue;}}}}}};if(!B((function(_1kg,_1kh){var _1ki=E(_1kg),_1kj=E(_1ki.a);if(E(_1kj.a)!=_1k5){return new F(function(){return _1k9(_1kh);});}else{if(E(_1kj.b)!=_1k6){return new F(function(){return _1k9(_1kh);});}else{var _1kk=u_iswlower(E(_1ki.b));if(!E(_1kk)){return false;}else{return new F(function(){return _1k9(_1kh);});}}}})(_dC,_dD))){_1jZ=_1k3;return __continue;}else{var _1kl=new T(function(){var _1km=function(_1kn){while(1){var _1ko=E(_1kn);if(!_1ko._){return false;}else{var _1kp=_1ko.b,_1kq=E(E(_1ko.a).a);if(E(_1kq.a)!=_1k5){_1kn=_1kp;continue;}else{if(E(_1kq.b)!=_1k6){_1kn=_1kp;continue;}else{return true;}}}}};if(!B((function(_1kr,_1ks){var _1kt=E(E(_1kr).a);if(E(_1kt.a)!=_1k5){return new F(function(){return _1km(_1ks);});}else{if(E(_1kt.b)!=_1k6){return new F(function(){return _1km(_1ks);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_1ku=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_1k5)==8){if(E(_1k6)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_1k5)==1){if(E(_1k6)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_1kv=new T(function(){var _1kw=function(_1kx){var _1ky=E(_1kx),_1kz=E(_1ky.a),_1kA=_1kz.b,_1kB=E(_1kz.a),_1kC=function(_1kD){return (_1kB!=_1fy)?true:(E(_1kA)!=_1gZ)?true:(E(_1ky.b)==66)?false:true;};if(_1kB!=_1k5){return new F(function(){return _1kC(_);});}else{if(E(_1kA)!=_1k6){return new F(function(){return _1kC(_);});}else{return false;}}};return B(_5R(_1kw,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1k5,_1k6),_aj),_1kv),b:_5J,c:_1ku,d:_ds,e:_1kl,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_1jY(_1k3));}));}}}}}}}}}})(_1jZ));if(_1k0!=__continue){return _1k0;}}};return B(_1jY(_1fv));}),_1kE=new T(function(){var _1kF=function(_1kG){while(1){var _1kH=E(_1kG);if(!_1kH._){return false;}else{var _1kI=_1kH.b,_1kJ=E(E(_1kH.a).a);if(E(_1kJ.a)!=_1fA){_1kG=_1kI;continue;}else{if(E(_1kJ.b)!=_1h0){_1kG=_1kI;continue;}else{return true;}}}}};if(!B((function(_1kK,_1kL){var _1kM=E(E(_1kK).a);if(E(_1kM.a)!=_1fA){return new F(function(){return _1kF(_1kL);});}else{if(E(_1kM.b)!=_1h0){return new F(function(){return _1kF(_1kL);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_1kN=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_1fA)==8){if(E(_1h0)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_1fA)==1){if(E(_1h0)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_dr))));}),_1kO=new T(function(){var _1kP=function(_1kQ){var _1kR=E(_1kQ),_1kS=E(_1kR.a),_1kT=_1kS.b,_1kU=E(_1kS.a),_1kV=function(_1kW){return (_1kU!=_1fy)?true:(E(_1kT)!=_1gZ)?true:(E(_1kR.b)==66)?false:true;};if(_1kU!=_1fA){return new F(function(){return _1kV(_);});}else{if(E(_1kT)!=_1h0){return new F(function(){return _1kV(_);});}else{return false;}}};return B(_5R(_1kP,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1fA,_1h0),_aj),_1kO),b:_5J,c:_1kN,d:_ds,e:_1kE,f:_8S,g:_8L,h:_8L,i:_5K},_1jX);}}}}}}}}}}else{return E(_1ft);}};return B(_1fp(_dC,_dD));}),_1kX=function(_1kY){while(1){var _1kZ=B((function(_1l0){var _1l1=E(_1l0);if(!_1l1._){return true;}else{var _1l2=_1l1.b,_1l3=E(E(_dC).a),_1l4=E(_1l1.a),_1l5=_1l4.b,_1l6=E(_1l4.a);if(E(_1l3.a)!=_1l6){var _1l7=function(_1l8){while(1){var _1l9=E(_1l8);if(!_1l9._){return true;}else{var _1la=_1l9.b,_1lb=E(E(_1l9.a).a);if(E(_1lb.a)!=_1l6){_1l8=_1la;continue;}else{if(E(_1lb.b)!=E(_1l5)){_1l8=_1la;continue;}else{return false;}}}}};if(!B(_1l7(_dD))){return false;}else{_1kY=_1l2;return __continue;}}else{var _1lc=E(_1l5);if(E(_1l3.b)!=_1lc){var _1ld=function(_1le){while(1){var _1lf=E(_1le);if(!_1lf._){return true;}else{var _1lg=_1lf.b,_1lh=E(E(_1lf.a).a);if(E(_1lh.a)!=_1l6){_1le=_1lg;continue;}else{if(E(_1lh.b)!=_1lc){_1le=_1lg;continue;}else{return false;}}}}};if(!B(_1ld(_dD))){return false;}else{_1kY=_1l2;return __continue;}}else{return false;}}}})(_1kY));if(_1kZ!=__continue){return _1kZ;}}},_1li=function(_1lj){var _1lk=E(_1lj);if(!_1lk._){return E(_VH);}else{var _1ll=E(_1lk.a),_1lm=_1ll.a,_1ln=new T(function(){return B(_1li(_1lk.b));});if(E(_1ll.b)==82){var _1lo=new T(function(){return B(_5B(0,new T(function(){var _1lp=E(_1lm);if(E(_1lp.a)==8){if(E(_1lp.b)==1){return true;}else{return E(_dA);}}else{return E(_dA);}}),B(_5B(1,new T(function(){var _1lq=E(_1lm);if(E(_1lq.a)==1){if(E(_1lq.b)==1){return true;}else{return E(_dz);}}else{return E(_dz);}}),_dr))));}),_1lr=E(_aK);if(!_1lr._){return E(_1ln);}else{var _1ls=_1lr.b,_1lt=E(_1lm),_1lu=_1lt.b,_1lv=E(_1lt.a),_1lw=E(_1lr.a),_1lx=_1lv+E(_1lw.a)|0;if(_1lx<1){var _1ly=function(_1lz){while(1){var _1lA=B((function(_1lB){var _1lC=E(_1lB);if(!_1lC._){return E(_1ln);}else{var _1lD=_1lC.b,_1lE=E(_1lC.a),_1lF=_1lv+E(_1lE.a)|0;if(_1lF<1){_1lz=_1lD;return __continue;}else{if(_1lF>8){_1lz=_1lD;return __continue;}else{var _1lG=E(_1lu),_1lH=_1lG+E(_1lE.b)|0;if(_1lH<1){_1lz=_1lD;return __continue;}else{if(_1lH>8){_1lz=_1lD;return __continue;}else{var _1lI=B(_4i(_1lv,_1lG,_1lF,_1lH));if(!_1lI._){return E(_cr);}else{var _1lJ=E(_1lI.b);if(!_1lJ._){return E(_8I);}else{if(!B(_1kX(B(_8D(_1lJ.a,_1lJ.b))))){_1lz=_1lD;return __continue;}else{var _1lK=function(_1lL){while(1){var _1lM=E(_1lL);if(!_1lM._){return true;}else{var _1lN=_1lM.b,_1lO=E(_1lM.a),_1lP=E(_1lO.a);if(E(_1lP.a)!=_1lF){_1lL=_1lN;continue;}else{if(E(_1lP.b)!=_1lH){_1lL=_1lN;continue;}else{var _1lQ=u_iswlower(E(_1lO.b));if(!E(_1lQ)){return false;}else{_1lL=_1lN;continue;}}}}}};if(!B((function(_1lR,_1lS){var _1lT=E(_1lR),_1lU=E(_1lT.a);if(E(_1lU.a)!=_1lF){return new F(function(){return _1lK(_1lS);});}else{if(E(_1lU.b)!=_1lH){return new F(function(){return _1lK(_1lS);});}else{var _1lV=u_iswlower(E(_1lT.b));if(!E(_1lV)){return false;}else{return new F(function(){return _1lK(_1lS);});}}}})(_dC,_dD))){_1lz=_1lD;return __continue;}else{var _1lW=new T(function(){var _1lX=function(_1lY){while(1){var _1lZ=E(_1lY);if(!_1lZ._){return false;}else{var _1m0=_1lZ.b,_1m1=E(E(_1lZ.a).a);if(E(_1m1.a)!=_1lF){_1lY=_1m0;continue;}else{if(E(_1m1.b)!=_1lH){_1lY=_1m0;continue;}else{return true;}}}}};if(!B((function(_1m2,_1m3){var _1m4=E(E(_1m2).a);if(E(_1m4.a)!=_1lF){return new F(function(){return _1lX(_1m3);});}else{if(E(_1m4.b)!=_1lH){return new F(function(){return _1lX(_1m3);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_1m5=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_1lF)==8){if(E(_1lH)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_1lF)==1){if(E(_1lH)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_1lo))));}),_1m6=new T(function(){var _1m7=function(_1m8){var _1m9=E(_1m8),_1ma=E(_1m9.a),_1mb=_1ma.b,_1mc=E(_1ma.a),_1md=function(_1me){return (_1mc!=_1lv)?true:(E(_1mb)!=_1lG)?true:(E(_1m9.b)==82)?false:true;};if(_1mc!=_1lF){return new F(function(){return _1md(_);});}else{if(E(_1mb)!=_1lH){return new F(function(){return _1md(_);});}else{return false;}}};return B(_5R(_1m7,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1lF,_1lH),_8T),_1m6),b:_5J,c:_1m5,d:_ds,e:_1lW,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_1ly(_1lD));}));}}}}}}}}}})(_1lz));if(_1lA!=__continue){return _1lA;}}};return new F(function(){return _1ly(_1ls);});}else{if(_1lx>8){var _1mf=function(_1mg){while(1){var _1mh=B((function(_1mi){var _1mj=E(_1mi);if(!_1mj._){return E(_1ln);}else{var _1mk=_1mj.b,_1ml=E(_1mj.a),_1mm=_1lv+E(_1ml.a)|0;if(_1mm<1){_1mg=_1mk;return __continue;}else{if(_1mm>8){_1mg=_1mk;return __continue;}else{var _1mn=E(_1lu),_1mo=_1mn+E(_1ml.b)|0;if(_1mo<1){_1mg=_1mk;return __continue;}else{if(_1mo>8){_1mg=_1mk;return __continue;}else{var _1mp=B(_4i(_1lv,_1mn,_1mm,_1mo));if(!_1mp._){return E(_cr);}else{var _1mq=E(_1mp.b);if(!_1mq._){return E(_8I);}else{if(!B(_1kX(B(_8D(_1mq.a,_1mq.b))))){_1mg=_1mk;return __continue;}else{var _1mr=function(_1ms){while(1){var _1mt=E(_1ms);if(!_1mt._){return true;}else{var _1mu=_1mt.b,_1mv=E(_1mt.a),_1mw=E(_1mv.a);if(E(_1mw.a)!=_1mm){_1ms=_1mu;continue;}else{if(E(_1mw.b)!=_1mo){_1ms=_1mu;continue;}else{var _1mx=u_iswlower(E(_1mv.b));if(!E(_1mx)){return false;}else{_1ms=_1mu;continue;}}}}}};if(!B((function(_1my,_1mz){var _1mA=E(_1my),_1mB=E(_1mA.a);if(E(_1mB.a)!=_1mm){return new F(function(){return _1mr(_1mz);});}else{if(E(_1mB.b)!=_1mo){return new F(function(){return _1mr(_1mz);});}else{var _1mC=u_iswlower(E(_1mA.b));if(!E(_1mC)){return false;}else{return new F(function(){return _1mr(_1mz);});}}}})(_dC,_dD))){_1mg=_1mk;return __continue;}else{var _1mD=new T(function(){var _1mE=function(_1mF){while(1){var _1mG=E(_1mF);if(!_1mG._){return false;}else{var _1mH=_1mG.b,_1mI=E(E(_1mG.a).a);if(E(_1mI.a)!=_1mm){_1mF=_1mH;continue;}else{if(E(_1mI.b)!=_1mo){_1mF=_1mH;continue;}else{return true;}}}}};if(!B((function(_1mJ,_1mK){var _1mL=E(E(_1mJ).a);if(E(_1mL.a)!=_1mm){return new F(function(){return _1mE(_1mK);});}else{if(E(_1mL.b)!=_1mo){return new F(function(){return _1mE(_1mK);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_1mM=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_1mm)==8){if(E(_1mo)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_1mm)==1){if(E(_1mo)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_1lo))));}),_1mN=new T(function(){var _1mO=function(_1mP){var _1mQ=E(_1mP),_1mR=E(_1mQ.a),_1mS=_1mR.b,_1mT=E(_1mR.a),_1mU=function(_1mV){return (_1mT!=_1lv)?true:(E(_1mS)!=_1mn)?true:(E(_1mQ.b)==82)?false:true;};if(_1mT!=_1mm){return new F(function(){return _1mU(_);});}else{if(E(_1mS)!=_1mo){return new F(function(){return _1mU(_);});}else{return false;}}};return B(_5R(_1mO,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1mm,_1mo),_8T),_1mN),b:_5J,c:_1mM,d:_ds,e:_1mD,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_1mf(_1mk));}));}}}}}}}}}})(_1mg));if(_1mh!=__continue){return _1mh;}}};return new F(function(){return _1mf(_1ls);});}else{var _1mW=E(_1lu),_1mX=_1mW+E(_1lw.b)|0;if(_1mX<1){var _1mY=function(_1mZ){while(1){var _1n0=B((function(_1n1){var _1n2=E(_1n1);if(!_1n2._){return E(_1ln);}else{var _1n3=_1n2.b,_1n4=E(_1n2.a),_1n5=_1lv+E(_1n4.a)|0;if(_1n5<1){_1mZ=_1n3;return __continue;}else{if(_1n5>8){_1mZ=_1n3;return __continue;}else{var _1n6=_1mW+E(_1n4.b)|0;if(_1n6<1){_1mZ=_1n3;return __continue;}else{if(_1n6>8){_1mZ=_1n3;return __continue;}else{var _1n7=B(_4i(_1lv,_1mW,_1n5,_1n6));if(!_1n7._){return E(_cr);}else{var _1n8=E(_1n7.b);if(!_1n8._){return E(_8I);}else{if(!B(_1kX(B(_8D(_1n8.a,_1n8.b))))){_1mZ=_1n3;return __continue;}else{var _1n9=function(_1na){while(1){var _1nb=E(_1na);if(!_1nb._){return true;}else{var _1nc=_1nb.b,_1nd=E(_1nb.a),_1ne=E(_1nd.a);if(E(_1ne.a)!=_1n5){_1na=_1nc;continue;}else{if(E(_1ne.b)!=_1n6){_1na=_1nc;continue;}else{var _1nf=u_iswlower(E(_1nd.b));if(!E(_1nf)){return false;}else{_1na=_1nc;continue;}}}}}};if(!B((function(_1ng,_1nh){var _1ni=E(_1ng),_1nj=E(_1ni.a);if(E(_1nj.a)!=_1n5){return new F(function(){return _1n9(_1nh);});}else{if(E(_1nj.b)!=_1n6){return new F(function(){return _1n9(_1nh);});}else{var _1nk=u_iswlower(E(_1ni.b));if(!E(_1nk)){return false;}else{return new F(function(){return _1n9(_1nh);});}}}})(_dC,_dD))){_1mZ=_1n3;return __continue;}else{var _1nl=new T(function(){var _1nm=function(_1nn){while(1){var _1no=E(_1nn);if(!_1no._){return false;}else{var _1np=_1no.b,_1nq=E(E(_1no.a).a);if(E(_1nq.a)!=_1n5){_1nn=_1np;continue;}else{if(E(_1nq.b)!=_1n6){_1nn=_1np;continue;}else{return true;}}}}};if(!B((function(_1nr,_1ns){var _1nt=E(E(_1nr).a);if(E(_1nt.a)!=_1n5){return new F(function(){return _1nm(_1ns);});}else{if(E(_1nt.b)!=_1n6){return new F(function(){return _1nm(_1ns);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_1nu=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_1n5)==8){if(E(_1n6)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_1n5)==1){if(E(_1n6)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_1lo))));}),_1nv=new T(function(){var _1nw=function(_1nx){var _1ny=E(_1nx),_1nz=E(_1ny.a),_1nA=_1nz.b,_1nB=E(_1nz.a),_1nC=function(_1nD){return (_1nB!=_1lv)?true:(E(_1nA)!=_1mW)?true:(E(_1ny.b)==82)?false:true;};if(_1nB!=_1n5){return new F(function(){return _1nC(_);});}else{if(E(_1nA)!=_1n6){return new F(function(){return _1nC(_);});}else{return false;}}};return B(_5R(_1nw,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1n5,_1n6),_8T),_1nv),b:_5J,c:_1nu,d:_ds,e:_1nl,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_1mY(_1n3));}));}}}}}}}}}})(_1mZ));if(_1n0!=__continue){return _1n0;}}};return new F(function(){return _1mY(_1ls);});}else{if(_1mX>8){var _1nE=function(_1nF){while(1){var _1nG=B((function(_1nH){var _1nI=E(_1nH);if(!_1nI._){return E(_1ln);}else{var _1nJ=_1nI.b,_1nK=E(_1nI.a),_1nL=_1lv+E(_1nK.a)|0;if(_1nL<1){_1nF=_1nJ;return __continue;}else{if(_1nL>8){_1nF=_1nJ;return __continue;}else{var _1nM=_1mW+E(_1nK.b)|0;if(_1nM<1){_1nF=_1nJ;return __continue;}else{if(_1nM>8){_1nF=_1nJ;return __continue;}else{var _1nN=B(_4i(_1lv,_1mW,_1nL,_1nM));if(!_1nN._){return E(_cr);}else{var _1nO=E(_1nN.b);if(!_1nO._){return E(_8I);}else{if(!B(_1kX(B(_8D(_1nO.a,_1nO.b))))){_1nF=_1nJ;return __continue;}else{var _1nP=function(_1nQ){while(1){var _1nR=E(_1nQ);if(!_1nR._){return true;}else{var _1nS=_1nR.b,_1nT=E(_1nR.a),_1nU=E(_1nT.a);if(E(_1nU.a)!=_1nL){_1nQ=_1nS;continue;}else{if(E(_1nU.b)!=_1nM){_1nQ=_1nS;continue;}else{var _1nV=u_iswlower(E(_1nT.b));if(!E(_1nV)){return false;}else{_1nQ=_1nS;continue;}}}}}};if(!B((function(_1nW,_1nX){var _1nY=E(_1nW),_1nZ=E(_1nY.a);if(E(_1nZ.a)!=_1nL){return new F(function(){return _1nP(_1nX);});}else{if(E(_1nZ.b)!=_1nM){return new F(function(){return _1nP(_1nX);});}else{var _1o0=u_iswlower(E(_1nY.b));if(!E(_1o0)){return false;}else{return new F(function(){return _1nP(_1nX);});}}}})(_dC,_dD))){_1nF=_1nJ;return __continue;}else{var _1o1=new T(function(){var _1o2=function(_1o3){while(1){var _1o4=E(_1o3);if(!_1o4._){return false;}else{var _1o5=_1o4.b,_1o6=E(E(_1o4.a).a);if(E(_1o6.a)!=_1nL){_1o3=_1o5;continue;}else{if(E(_1o6.b)!=_1nM){_1o3=_1o5;continue;}else{return true;}}}}};if(!B((function(_1o7,_1o8){var _1o9=E(E(_1o7).a);if(E(_1o9.a)!=_1nL){return new F(function(){return _1o2(_1o8);});}else{if(E(_1o9.b)!=_1nM){return new F(function(){return _1o2(_1o8);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_1oa=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_1nL)==8){if(E(_1nM)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_1nL)==1){if(E(_1nM)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_1lo))));}),_1ob=new T(function(){var _1oc=function(_1od){var _1oe=E(_1od),_1of=E(_1oe.a),_1og=_1of.b,_1oh=E(_1of.a),_1oi=function(_1oj){return (_1oh!=_1lv)?true:(E(_1og)!=_1mW)?true:(E(_1oe.b)==82)?false:true;};if(_1oh!=_1nL){return new F(function(){return _1oi(_);});}else{if(E(_1og)!=_1nM){return new F(function(){return _1oi(_);});}else{return false;}}};return B(_5R(_1oc,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1nL,_1nM),_8T),_1ob),b:_5J,c:_1oa,d:_ds,e:_1o1,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_1nE(_1nJ));}));}}}}}}}}}})(_1nF));if(_1nG!=__continue){return _1nG;}}};return new F(function(){return _1nE(_1ls);});}else{var _1ok=B(_4i(_1lv,_1mW,_1lx,_1mX));if(!_1ok._){return E(_cr);}else{var _1ol=E(_1ok.b);if(!_1ol._){return E(_8I);}else{if(!B(_1kX(B(_8D(_1ol.a,_1ol.b))))){var _1om=function(_1on){while(1){var _1oo=B((function(_1op){var _1oq=E(_1op);if(!_1oq._){return E(_1ln);}else{var _1or=_1oq.b,_1os=E(_1oq.a),_1ot=_1lv+E(_1os.a)|0;if(_1ot<1){_1on=_1or;return __continue;}else{if(_1ot>8){_1on=_1or;return __continue;}else{var _1ou=_1mW+E(_1os.b)|0;if(_1ou<1){_1on=_1or;return __continue;}else{if(_1ou>8){_1on=_1or;return __continue;}else{var _1ov=B(_4i(_1lv,_1mW,_1ot,_1ou));if(!_1ov._){return E(_cr);}else{var _1ow=E(_1ov.b);if(!_1ow._){return E(_8I);}else{if(!B(_1kX(B(_8D(_1ow.a,_1ow.b))))){_1on=_1or;return __continue;}else{var _1ox=function(_1oy){while(1){var _1oz=E(_1oy);if(!_1oz._){return true;}else{var _1oA=_1oz.b,_1oB=E(_1oz.a),_1oC=E(_1oB.a);if(E(_1oC.a)!=_1ot){_1oy=_1oA;continue;}else{if(E(_1oC.b)!=_1ou){_1oy=_1oA;continue;}else{var _1oD=u_iswlower(E(_1oB.b));if(!E(_1oD)){return false;}else{_1oy=_1oA;continue;}}}}}};if(!B((function(_1oE,_1oF){var _1oG=E(_1oE),_1oH=E(_1oG.a);if(E(_1oH.a)!=_1ot){return new F(function(){return _1ox(_1oF);});}else{if(E(_1oH.b)!=_1ou){return new F(function(){return _1ox(_1oF);});}else{var _1oI=u_iswlower(E(_1oG.b));if(!E(_1oI)){return false;}else{return new F(function(){return _1ox(_1oF);});}}}})(_dC,_dD))){_1on=_1or;return __continue;}else{var _1oJ=new T(function(){var _1oK=function(_1oL){while(1){var _1oM=E(_1oL);if(!_1oM._){return false;}else{var _1oN=_1oM.b,_1oO=E(E(_1oM.a).a);if(E(_1oO.a)!=_1ot){_1oL=_1oN;continue;}else{if(E(_1oO.b)!=_1ou){_1oL=_1oN;continue;}else{return true;}}}}};if(!B((function(_1oP,_1oQ){var _1oR=E(E(_1oP).a);if(E(_1oR.a)!=_1ot){return new F(function(){return _1oK(_1oQ);});}else{if(E(_1oR.b)!=_1ou){return new F(function(){return _1oK(_1oQ);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_1oS=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_1ot)==8){if(E(_1ou)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_1ot)==1){if(E(_1ou)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_1lo))));}),_1oT=new T(function(){var _1oU=function(_1oV){var _1oW=E(_1oV),_1oX=E(_1oW.a),_1oY=_1oX.b,_1oZ=E(_1oX.a),_1p0=function(_1p1){return (_1oZ!=_1lv)?true:(E(_1oY)!=_1mW)?true:(E(_1oW.b)==82)?false:true;};if(_1oZ!=_1ot){return new F(function(){return _1p0(_);});}else{if(E(_1oY)!=_1ou){return new F(function(){return _1p0(_);});}else{return false;}}};return B(_5R(_1oU,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1ot,_1ou),_8T),_1oT),b:_5J,c:_1oS,d:_ds,e:_1oJ,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_1om(_1or));}));}}}}}}}}}})(_1on));if(_1oo!=__continue){return _1oo;}}};return new F(function(){return _1om(_1ls);});}else{var _1p2=function(_1p3){while(1){var _1p4=E(_1p3);if(!_1p4._){return true;}else{var _1p5=_1p4.b,_1p6=E(_1p4.a),_1p7=E(_1p6.a);if(E(_1p7.a)!=_1lx){_1p3=_1p5;continue;}else{if(E(_1p7.b)!=_1mX){_1p3=_1p5;continue;}else{var _1p8=u_iswlower(E(_1p6.b));if(!E(_1p8)){return false;}else{_1p3=_1p5;continue;}}}}}};if(!B((function(_1p9,_1pa){var _1pb=E(_1p9),_1pc=E(_1pb.a);if(E(_1pc.a)!=_1lx){return new F(function(){return _1p2(_1pa);});}else{if(E(_1pc.b)!=_1mX){return new F(function(){return _1p2(_1pa);});}else{var _1pd=u_iswlower(E(_1pb.b));if(!E(_1pd)){return false;}else{return new F(function(){return _1p2(_1pa);});}}}})(_dC,_dD))){var _1pe=function(_1pf){while(1){var _1pg=B((function(_1ph){var _1pi=E(_1ph);if(!_1pi._){return E(_1ln);}else{var _1pj=_1pi.b,_1pk=E(_1pi.a),_1pl=_1lv+E(_1pk.a)|0;if(_1pl<1){_1pf=_1pj;return __continue;}else{if(_1pl>8){_1pf=_1pj;return __continue;}else{var _1pm=_1mW+E(_1pk.b)|0;if(_1pm<1){_1pf=_1pj;return __continue;}else{if(_1pm>8){_1pf=_1pj;return __continue;}else{var _1pn=B(_4i(_1lv,_1mW,_1pl,_1pm));if(!_1pn._){return E(_cr);}else{var _1po=E(_1pn.b);if(!_1po._){return E(_8I);}else{if(!B(_1kX(B(_8D(_1po.a,_1po.b))))){_1pf=_1pj;return __continue;}else{var _1pp=function(_1pq){while(1){var _1pr=E(_1pq);if(!_1pr._){return true;}else{var _1ps=_1pr.b,_1pt=E(_1pr.a),_1pu=E(_1pt.a);if(E(_1pu.a)!=_1pl){_1pq=_1ps;continue;}else{if(E(_1pu.b)!=_1pm){_1pq=_1ps;continue;}else{var _1pv=u_iswlower(E(_1pt.b));if(!E(_1pv)){return false;}else{_1pq=_1ps;continue;}}}}}};if(!B((function(_1pw,_1px){var _1py=E(_1pw),_1pz=E(_1py.a);if(E(_1pz.a)!=_1pl){return new F(function(){return _1pp(_1px);});}else{if(E(_1pz.b)!=_1pm){return new F(function(){return _1pp(_1px);});}else{var _1pA=u_iswlower(E(_1py.b));if(!E(_1pA)){return false;}else{return new F(function(){return _1pp(_1px);});}}}})(_dC,_dD))){_1pf=_1pj;return __continue;}else{var _1pB=new T(function(){var _1pC=function(_1pD){while(1){var _1pE=E(_1pD);if(!_1pE._){return false;}else{var _1pF=_1pE.b,_1pG=E(E(_1pE.a).a);if(E(_1pG.a)!=_1pl){_1pD=_1pF;continue;}else{if(E(_1pG.b)!=_1pm){_1pD=_1pF;continue;}else{return true;}}}}};if(!B((function(_1pH,_1pI){var _1pJ=E(E(_1pH).a);if(E(_1pJ.a)!=_1pl){return new F(function(){return _1pC(_1pI);});}else{if(E(_1pJ.b)!=_1pm){return new F(function(){return _1pC(_1pI);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_1pK=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_1pl)==8){if(E(_1pm)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_1pl)==1){if(E(_1pm)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_1lo))));}),_1pL=new T(function(){var _1pM=function(_1pN){var _1pO=E(_1pN),_1pP=E(_1pO.a),_1pQ=_1pP.b,_1pR=E(_1pP.a),_1pS=function(_1pT){return (_1pR!=_1lv)?true:(E(_1pQ)!=_1mW)?true:(E(_1pO.b)==82)?false:true;};if(_1pR!=_1pl){return new F(function(){return _1pS(_);});}else{if(E(_1pQ)!=_1pm){return new F(function(){return _1pS(_);});}else{return false;}}};return B(_5R(_1pM,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1pl,_1pm),_8T),_1pL),b:_5J,c:_1pK,d:_ds,e:_1pB,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_1pe(_1pj));}));}}}}}}}}}})(_1pf));if(_1pg!=__continue){return _1pg;}}};return new F(function(){return _1pe(_1ls);});}else{var _1pU=new T(function(){var _1pV=function(_1pW){while(1){var _1pX=B((function(_1pY){var _1pZ=E(_1pY);if(!_1pZ._){return E(_1ln);}else{var _1q0=_1pZ.b,_1q1=E(_1pZ.a),_1q2=_1lv+E(_1q1.a)|0;if(_1q2<1){_1pW=_1q0;return __continue;}else{if(_1q2>8){_1pW=_1q0;return __continue;}else{var _1q3=_1mW+E(_1q1.b)|0;if(_1q3<1){_1pW=_1q0;return __continue;}else{if(_1q3>8){_1pW=_1q0;return __continue;}else{var _1q4=B(_4i(_1lv,_1mW,_1q2,_1q3));if(!_1q4._){return E(_cr);}else{var _1q5=E(_1q4.b);if(!_1q5._){return E(_8I);}else{if(!B(_1kX(B(_8D(_1q5.a,_1q5.b))))){_1pW=_1q0;return __continue;}else{var _1q6=function(_1q7){while(1){var _1q8=E(_1q7);if(!_1q8._){return true;}else{var _1q9=_1q8.b,_1qa=E(_1q8.a),_1qb=E(_1qa.a);if(E(_1qb.a)!=_1q2){_1q7=_1q9;continue;}else{if(E(_1qb.b)!=_1q3){_1q7=_1q9;continue;}else{var _1qc=u_iswlower(E(_1qa.b));if(!E(_1qc)){return false;}else{_1q7=_1q9;continue;}}}}}};if(!B((function(_1qd,_1qe){var _1qf=E(_1qd),_1qg=E(_1qf.a);if(E(_1qg.a)!=_1q2){return new F(function(){return _1q6(_1qe);});}else{if(E(_1qg.b)!=_1q3){return new F(function(){return _1q6(_1qe);});}else{var _1qh=u_iswlower(E(_1qf.b));if(!E(_1qh)){return false;}else{return new F(function(){return _1q6(_1qe);});}}}})(_dC,_dD))){_1pW=_1q0;return __continue;}else{var _1qi=new T(function(){var _1qj=function(_1qk){while(1){var _1ql=E(_1qk);if(!_1ql._){return false;}else{var _1qm=_1ql.b,_1qn=E(E(_1ql.a).a);if(E(_1qn.a)!=_1q2){_1qk=_1qm;continue;}else{if(E(_1qn.b)!=_1q3){_1qk=_1qm;continue;}else{return true;}}}}};if(!B((function(_1qo,_1qp){var _1qq=E(E(_1qo).a);if(E(_1qq.a)!=_1q2){return new F(function(){return _1qj(_1qp);});}else{if(E(_1qq.b)!=_1q3){return new F(function(){return _1qj(_1qp);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_1qr=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_1q2)==8){if(E(_1q3)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_1q2)==1){if(E(_1q3)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_1lo))));}),_1qs=new T(function(){var _1qt=function(_1qu){var _1qv=E(_1qu),_1qw=E(_1qv.a),_1qx=_1qw.b,_1qy=E(_1qw.a),_1qz=function(_1qA){return (_1qy!=_1lv)?true:(E(_1qx)!=_1mW)?true:(E(_1qv.b)==82)?false:true;};if(_1qy!=_1q2){return new F(function(){return _1qz(_);});}else{if(E(_1qx)!=_1q3){return new F(function(){return _1qz(_);});}else{return false;}}};return B(_5R(_1qt,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1q2,_1q3),_8T),_1qs),b:_5J,c:_1qr,d:_ds,e:_1qi,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_1pV(_1q0));}));}}}}}}}}}})(_1pW));if(_1pX!=__continue){return _1pX;}}};return B(_1pV(_1ls));}),_1qB=new T(function(){var _1qC=function(_1qD){while(1){var _1qE=E(_1qD);if(!_1qE._){return false;}else{var _1qF=_1qE.b,_1qG=E(E(_1qE.a).a);if(E(_1qG.a)!=_1lx){_1qD=_1qF;continue;}else{if(E(_1qG.b)!=_1mX){_1qD=_1qF;continue;}else{return true;}}}}};if(!B((function(_1qH,_1qI){var _1qJ=E(E(_1qH).a);if(E(_1qJ.a)!=_1lx){return new F(function(){return _1qC(_1qI);});}else{if(E(_1qJ.b)!=_1mX){return new F(function(){return _1qC(_1qI);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_1qK=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_1lx)==8){if(E(_1mX)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_1lx)==1){if(E(_1mX)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_1lo))));}),_1qL=new T(function(){var _1qM=function(_1qN){var _1qO=E(_1qN),_1qP=E(_1qO.a),_1qQ=_1qP.b,_1qR=E(_1qP.a),_1qS=function(_1qT){return (_1qR!=_1lv)?true:(E(_1qQ)!=_1mW)?true:(E(_1qO.b)==82)?false:true;};if(_1qR!=_1lx){return new F(function(){return _1qS(_);});}else{if(E(_1qQ)!=_1mX){return new F(function(){return _1qS(_);});}else{return false;}}};return B(_5R(_1qM,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1lx,_1mX),_8T),_1qL),b:_5J,c:_1qK,d:_ds,e:_1qB,f:_8S,g:_8L,h:_8L,i:_5K},_1pU);}}}}}}}}}}else{return E(_1ln);}}},_1qU=function(_1qV,_1qW){var _1qX=E(_1qV),_1qY=_1qX.a,_1qZ=new T(function(){return B(_1li(_1qW));});if(E(_1qX.b)==82){var _1r0=new T(function(){return B(_5B(0,new T(function(){var _1r1=E(_1qY);if(E(_1r1.a)==8){if(E(_1r1.b)==1){return true;}else{return E(_dA);}}else{return E(_dA);}}),B(_5B(1,new T(function(){var _1r2=E(_1qY);if(E(_1r2.a)==1){if(E(_1r2.b)==1){return true;}else{return E(_dz);}}else{return E(_dz);}}),_dr))));}),_1r3=E(_aK);if(!_1r3._){return E(_1qZ);}else{var _1r4=_1r3.b,_1r5=E(_1qY),_1r6=_1r5.b,_1r7=E(_1r5.a),_1r8=E(_1r3.a),_1r9=_1r7+E(_1r8.a)|0;if(_1r9<1){var _1ra=function(_1rb){while(1){var _1rc=B((function(_1rd){var _1re=E(_1rd);if(!_1re._){return E(_1qZ);}else{var _1rf=_1re.b,_1rg=E(_1re.a),_1rh=_1r7+E(_1rg.a)|0;if(_1rh<1){_1rb=_1rf;return __continue;}else{if(_1rh>8){_1rb=_1rf;return __continue;}else{var _1ri=E(_1r6),_1rj=_1ri+E(_1rg.b)|0;if(_1rj<1){_1rb=_1rf;return __continue;}else{if(_1rj>8){_1rb=_1rf;return __continue;}else{var _1rk=B(_4i(_1r7,_1ri,_1rh,_1rj));if(!_1rk._){return E(_cr);}else{var _1rl=E(_1rk.b);if(!_1rl._){return E(_8I);}else{if(!B(_1kX(B(_8D(_1rl.a,_1rl.b))))){_1rb=_1rf;return __continue;}else{var _1rm=function(_1rn){while(1){var _1ro=E(_1rn);if(!_1ro._){return true;}else{var _1rp=_1ro.b,_1rq=E(_1ro.a),_1rr=E(_1rq.a);if(E(_1rr.a)!=_1rh){_1rn=_1rp;continue;}else{if(E(_1rr.b)!=_1rj){_1rn=_1rp;continue;}else{var _1rs=u_iswlower(E(_1rq.b));if(!E(_1rs)){return false;}else{_1rn=_1rp;continue;}}}}}};if(!B((function(_1rt,_1ru){var _1rv=E(_1rt),_1rw=E(_1rv.a);if(E(_1rw.a)!=_1rh){return new F(function(){return _1rm(_1ru);});}else{if(E(_1rw.b)!=_1rj){return new F(function(){return _1rm(_1ru);});}else{var _1rx=u_iswlower(E(_1rv.b));if(!E(_1rx)){return false;}else{return new F(function(){return _1rm(_1ru);});}}}})(_dC,_dD))){_1rb=_1rf;return __continue;}else{var _1ry=new T(function(){var _1rz=function(_1rA){while(1){var _1rB=E(_1rA);if(!_1rB._){return false;}else{var _1rC=_1rB.b,_1rD=E(E(_1rB.a).a);if(E(_1rD.a)!=_1rh){_1rA=_1rC;continue;}else{if(E(_1rD.b)!=_1rj){_1rA=_1rC;continue;}else{return true;}}}}};if(!B((function(_1rE,_1rF){var _1rG=E(E(_1rE).a);if(E(_1rG.a)!=_1rh){return new F(function(){return _1rz(_1rF);});}else{if(E(_1rG.b)!=_1rj){return new F(function(){return _1rz(_1rF);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_1rH=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_1rh)==8){if(E(_1rj)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_1rh)==1){if(E(_1rj)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_1r0))));}),_1rI=new T(function(){var _1rJ=function(_1rK){var _1rL=E(_1rK),_1rM=E(_1rL.a),_1rN=_1rM.b,_1rO=E(_1rM.a),_1rP=function(_1rQ){return (_1rO!=_1r7)?true:(E(_1rN)!=_1ri)?true:(E(_1rL.b)==82)?false:true;};if(_1rO!=_1rh){return new F(function(){return _1rP(_);});}else{if(E(_1rN)!=_1rj){return new F(function(){return _1rP(_);});}else{return false;}}};return B(_5R(_1rJ,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1rh,_1rj),_8T),_1rI),b:_5J,c:_1rH,d:_ds,e:_1ry,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_1ra(_1rf));}));}}}}}}}}}})(_1rb));if(_1rc!=__continue){return _1rc;}}};return new F(function(){return _1ra(_1r4);});}else{if(_1r9>8){var _1rR=function(_1rS){while(1){var _1rT=B((function(_1rU){var _1rV=E(_1rU);if(!_1rV._){return E(_1qZ);}else{var _1rW=_1rV.b,_1rX=E(_1rV.a),_1rY=_1r7+E(_1rX.a)|0;if(_1rY<1){_1rS=_1rW;return __continue;}else{if(_1rY>8){_1rS=_1rW;return __continue;}else{var _1rZ=E(_1r6),_1s0=_1rZ+E(_1rX.b)|0;if(_1s0<1){_1rS=_1rW;return __continue;}else{if(_1s0>8){_1rS=_1rW;return __continue;}else{var _1s1=B(_4i(_1r7,_1rZ,_1rY,_1s0));if(!_1s1._){return E(_cr);}else{var _1s2=E(_1s1.b);if(!_1s2._){return E(_8I);}else{if(!B(_1kX(B(_8D(_1s2.a,_1s2.b))))){_1rS=_1rW;return __continue;}else{var _1s3=function(_1s4){while(1){var _1s5=E(_1s4);if(!_1s5._){return true;}else{var _1s6=_1s5.b,_1s7=E(_1s5.a),_1s8=E(_1s7.a);if(E(_1s8.a)!=_1rY){_1s4=_1s6;continue;}else{if(E(_1s8.b)!=_1s0){_1s4=_1s6;continue;}else{var _1s9=u_iswlower(E(_1s7.b));if(!E(_1s9)){return false;}else{_1s4=_1s6;continue;}}}}}};if(!B((function(_1sa,_1sb){var _1sc=E(_1sa),_1sd=E(_1sc.a);if(E(_1sd.a)!=_1rY){return new F(function(){return _1s3(_1sb);});}else{if(E(_1sd.b)!=_1s0){return new F(function(){return _1s3(_1sb);});}else{var _1se=u_iswlower(E(_1sc.b));if(!E(_1se)){return false;}else{return new F(function(){return _1s3(_1sb);});}}}})(_dC,_dD))){_1rS=_1rW;return __continue;}else{var _1sf=new T(function(){var _1sg=function(_1sh){while(1){var _1si=E(_1sh);if(!_1si._){return false;}else{var _1sj=_1si.b,_1sk=E(E(_1si.a).a);if(E(_1sk.a)!=_1rY){_1sh=_1sj;continue;}else{if(E(_1sk.b)!=_1s0){_1sh=_1sj;continue;}else{return true;}}}}};if(!B((function(_1sl,_1sm){var _1sn=E(E(_1sl).a);if(E(_1sn.a)!=_1rY){return new F(function(){return _1sg(_1sm);});}else{if(E(_1sn.b)!=_1s0){return new F(function(){return _1sg(_1sm);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_1so=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_1rY)==8){if(E(_1s0)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_1rY)==1){if(E(_1s0)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_1r0))));}),_1sp=new T(function(){var _1sq=function(_1sr){var _1ss=E(_1sr),_1st=E(_1ss.a),_1su=_1st.b,_1sv=E(_1st.a),_1sw=function(_1sx){return (_1sv!=_1r7)?true:(E(_1su)!=_1rZ)?true:(E(_1ss.b)==82)?false:true;};if(_1sv!=_1rY){return new F(function(){return _1sw(_);});}else{if(E(_1su)!=_1s0){return new F(function(){return _1sw(_);});}else{return false;}}};return B(_5R(_1sq,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1rY,_1s0),_8T),_1sp),b:_5J,c:_1so,d:_ds,e:_1sf,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_1rR(_1rW));}));}}}}}}}}}})(_1rS));if(_1rT!=__continue){return _1rT;}}};return new F(function(){return _1rR(_1r4);});}else{var _1sy=E(_1r6),_1sz=_1sy+E(_1r8.b)|0;if(_1sz<1){var _1sA=function(_1sB){while(1){var _1sC=B((function(_1sD){var _1sE=E(_1sD);if(!_1sE._){return E(_1qZ);}else{var _1sF=_1sE.b,_1sG=E(_1sE.a),_1sH=_1r7+E(_1sG.a)|0;if(_1sH<1){_1sB=_1sF;return __continue;}else{if(_1sH>8){_1sB=_1sF;return __continue;}else{var _1sI=_1sy+E(_1sG.b)|0;if(_1sI<1){_1sB=_1sF;return __continue;}else{if(_1sI>8){_1sB=_1sF;return __continue;}else{var _1sJ=B(_4i(_1r7,_1sy,_1sH,_1sI));if(!_1sJ._){return E(_cr);}else{var _1sK=E(_1sJ.b);if(!_1sK._){return E(_8I);}else{if(!B(_1kX(B(_8D(_1sK.a,_1sK.b))))){_1sB=_1sF;return __continue;}else{var _1sL=function(_1sM){while(1){var _1sN=E(_1sM);if(!_1sN._){return true;}else{var _1sO=_1sN.b,_1sP=E(_1sN.a),_1sQ=E(_1sP.a);if(E(_1sQ.a)!=_1sH){_1sM=_1sO;continue;}else{if(E(_1sQ.b)!=_1sI){_1sM=_1sO;continue;}else{var _1sR=u_iswlower(E(_1sP.b));if(!E(_1sR)){return false;}else{_1sM=_1sO;continue;}}}}}};if(!B((function(_1sS,_1sT){var _1sU=E(_1sS),_1sV=E(_1sU.a);if(E(_1sV.a)!=_1sH){return new F(function(){return _1sL(_1sT);});}else{if(E(_1sV.b)!=_1sI){return new F(function(){return _1sL(_1sT);});}else{var _1sW=u_iswlower(E(_1sU.b));if(!E(_1sW)){return false;}else{return new F(function(){return _1sL(_1sT);});}}}})(_dC,_dD))){_1sB=_1sF;return __continue;}else{var _1sX=new T(function(){var _1sY=function(_1sZ){while(1){var _1t0=E(_1sZ);if(!_1t0._){return false;}else{var _1t1=_1t0.b,_1t2=E(E(_1t0.a).a);if(E(_1t2.a)!=_1sH){_1sZ=_1t1;continue;}else{if(E(_1t2.b)!=_1sI){_1sZ=_1t1;continue;}else{return true;}}}}};if(!B((function(_1t3,_1t4){var _1t5=E(E(_1t3).a);if(E(_1t5.a)!=_1sH){return new F(function(){return _1sY(_1t4);});}else{if(E(_1t5.b)!=_1sI){return new F(function(){return _1sY(_1t4);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_1t6=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_1sH)==8){if(E(_1sI)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_1sH)==1){if(E(_1sI)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_1r0))));}),_1t7=new T(function(){var _1t8=function(_1t9){var _1ta=E(_1t9),_1tb=E(_1ta.a),_1tc=_1tb.b,_1td=E(_1tb.a),_1te=function(_1tf){return (_1td!=_1r7)?true:(E(_1tc)!=_1sy)?true:(E(_1ta.b)==82)?false:true;};if(_1td!=_1sH){return new F(function(){return _1te(_);});}else{if(E(_1tc)!=_1sI){return new F(function(){return _1te(_);});}else{return false;}}};return B(_5R(_1t8,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1sH,_1sI),_8T),_1t7),b:_5J,c:_1t6,d:_ds,e:_1sX,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_1sA(_1sF));}));}}}}}}}}}})(_1sB));if(_1sC!=__continue){return _1sC;}}};return new F(function(){return _1sA(_1r4);});}else{if(_1sz>8){var _1tg=function(_1th){while(1){var _1ti=B((function(_1tj){var _1tk=E(_1tj);if(!_1tk._){return E(_1qZ);}else{var _1tl=_1tk.b,_1tm=E(_1tk.a),_1tn=_1r7+E(_1tm.a)|0;if(_1tn<1){_1th=_1tl;return __continue;}else{if(_1tn>8){_1th=_1tl;return __continue;}else{var _1to=_1sy+E(_1tm.b)|0;if(_1to<1){_1th=_1tl;return __continue;}else{if(_1to>8){_1th=_1tl;return __continue;}else{var _1tp=B(_4i(_1r7,_1sy,_1tn,_1to));if(!_1tp._){return E(_cr);}else{var _1tq=E(_1tp.b);if(!_1tq._){return E(_8I);}else{if(!B(_1kX(B(_8D(_1tq.a,_1tq.b))))){_1th=_1tl;return __continue;}else{var _1tr=function(_1ts){while(1){var _1tt=E(_1ts);if(!_1tt._){return true;}else{var _1tu=_1tt.b,_1tv=E(_1tt.a),_1tw=E(_1tv.a);if(E(_1tw.a)!=_1tn){_1ts=_1tu;continue;}else{if(E(_1tw.b)!=_1to){_1ts=_1tu;continue;}else{var _1tx=u_iswlower(E(_1tv.b));if(!E(_1tx)){return false;}else{_1ts=_1tu;continue;}}}}}};if(!B((function(_1ty,_1tz){var _1tA=E(_1ty),_1tB=E(_1tA.a);if(E(_1tB.a)!=_1tn){return new F(function(){return _1tr(_1tz);});}else{if(E(_1tB.b)!=_1to){return new F(function(){return _1tr(_1tz);});}else{var _1tC=u_iswlower(E(_1tA.b));if(!E(_1tC)){return false;}else{return new F(function(){return _1tr(_1tz);});}}}})(_dC,_dD))){_1th=_1tl;return __continue;}else{var _1tD=new T(function(){var _1tE=function(_1tF){while(1){var _1tG=E(_1tF);if(!_1tG._){return false;}else{var _1tH=_1tG.b,_1tI=E(E(_1tG.a).a);if(E(_1tI.a)!=_1tn){_1tF=_1tH;continue;}else{if(E(_1tI.b)!=_1to){_1tF=_1tH;continue;}else{return true;}}}}};if(!B((function(_1tJ,_1tK){var _1tL=E(E(_1tJ).a);if(E(_1tL.a)!=_1tn){return new F(function(){return _1tE(_1tK);});}else{if(E(_1tL.b)!=_1to){return new F(function(){return _1tE(_1tK);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_1tM=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_1tn)==8){if(E(_1to)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_1tn)==1){if(E(_1to)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_1r0))));}),_1tN=new T(function(){var _1tO=function(_1tP){var _1tQ=E(_1tP),_1tR=E(_1tQ.a),_1tS=_1tR.b,_1tT=E(_1tR.a),_1tU=function(_1tV){return (_1tT!=_1r7)?true:(E(_1tS)!=_1sy)?true:(E(_1tQ.b)==82)?false:true;};if(_1tT!=_1tn){return new F(function(){return _1tU(_);});}else{if(E(_1tS)!=_1to){return new F(function(){return _1tU(_);});}else{return false;}}};return B(_5R(_1tO,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1tn,_1to),_8T),_1tN),b:_5J,c:_1tM,d:_ds,e:_1tD,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_1tg(_1tl));}));}}}}}}}}}})(_1th));if(_1ti!=__continue){return _1ti;}}};return new F(function(){return _1tg(_1r4);});}else{var _1tW=B(_4i(_1r7,_1sy,_1r9,_1sz));if(!_1tW._){return E(_cr);}else{var _1tX=E(_1tW.b);if(!_1tX._){return E(_8I);}else{if(!B(_1kX(B(_8D(_1tX.a,_1tX.b))))){var _1tY=function(_1tZ){while(1){var _1u0=B((function(_1u1){var _1u2=E(_1u1);if(!_1u2._){return E(_1qZ);}else{var _1u3=_1u2.b,_1u4=E(_1u2.a),_1u5=_1r7+E(_1u4.a)|0;if(_1u5<1){_1tZ=_1u3;return __continue;}else{if(_1u5>8){_1tZ=_1u3;return __continue;}else{var _1u6=_1sy+E(_1u4.b)|0;if(_1u6<1){_1tZ=_1u3;return __continue;}else{if(_1u6>8){_1tZ=_1u3;return __continue;}else{var _1u7=B(_4i(_1r7,_1sy,_1u5,_1u6));if(!_1u7._){return E(_cr);}else{var _1u8=E(_1u7.b);if(!_1u8._){return E(_8I);}else{if(!B(_1kX(B(_8D(_1u8.a,_1u8.b))))){_1tZ=_1u3;return __continue;}else{var _1u9=function(_1ua){while(1){var _1ub=E(_1ua);if(!_1ub._){return true;}else{var _1uc=_1ub.b,_1ud=E(_1ub.a),_1ue=E(_1ud.a);if(E(_1ue.a)!=_1u5){_1ua=_1uc;continue;}else{if(E(_1ue.b)!=_1u6){_1ua=_1uc;continue;}else{var _1uf=u_iswlower(E(_1ud.b));if(!E(_1uf)){return false;}else{_1ua=_1uc;continue;}}}}}};if(!B((function(_1ug,_1uh){var _1ui=E(_1ug),_1uj=E(_1ui.a);if(E(_1uj.a)!=_1u5){return new F(function(){return _1u9(_1uh);});}else{if(E(_1uj.b)!=_1u6){return new F(function(){return _1u9(_1uh);});}else{var _1uk=u_iswlower(E(_1ui.b));if(!E(_1uk)){return false;}else{return new F(function(){return _1u9(_1uh);});}}}})(_dC,_dD))){_1tZ=_1u3;return __continue;}else{var _1ul=new T(function(){var _1um=function(_1un){while(1){var _1uo=E(_1un);if(!_1uo._){return false;}else{var _1up=_1uo.b,_1uq=E(E(_1uo.a).a);if(E(_1uq.a)!=_1u5){_1un=_1up;continue;}else{if(E(_1uq.b)!=_1u6){_1un=_1up;continue;}else{return true;}}}}};if(!B((function(_1ur,_1us){var _1ut=E(E(_1ur).a);if(E(_1ut.a)!=_1u5){return new F(function(){return _1um(_1us);});}else{if(E(_1ut.b)!=_1u6){return new F(function(){return _1um(_1us);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_1uu=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_1u5)==8){if(E(_1u6)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_1u5)==1){if(E(_1u6)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_1r0))));}),_1uv=new T(function(){var _1uw=function(_1ux){var _1uy=E(_1ux),_1uz=E(_1uy.a),_1uA=_1uz.b,_1uB=E(_1uz.a),_1uC=function(_1uD){return (_1uB!=_1r7)?true:(E(_1uA)!=_1sy)?true:(E(_1uy.b)==82)?false:true;};if(_1uB!=_1u5){return new F(function(){return _1uC(_);});}else{if(E(_1uA)!=_1u6){return new F(function(){return _1uC(_);});}else{return false;}}};return B(_5R(_1uw,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1u5,_1u6),_8T),_1uv),b:_5J,c:_1uu,d:_ds,e:_1ul,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_1tY(_1u3));}));}}}}}}}}}})(_1tZ));if(_1u0!=__continue){return _1u0;}}};return new F(function(){return _1tY(_1r4);});}else{var _1uE=function(_1uF){while(1){var _1uG=E(_1uF);if(!_1uG._){return true;}else{var _1uH=_1uG.b,_1uI=E(_1uG.a),_1uJ=E(_1uI.a);if(E(_1uJ.a)!=_1r9){_1uF=_1uH;continue;}else{if(E(_1uJ.b)!=_1sz){_1uF=_1uH;continue;}else{var _1uK=u_iswlower(E(_1uI.b));if(!E(_1uK)){return false;}else{_1uF=_1uH;continue;}}}}}};if(!B((function(_1uL,_1uM){var _1uN=E(_1uL),_1uO=E(_1uN.a);if(E(_1uO.a)!=_1r9){return new F(function(){return _1uE(_1uM);});}else{if(E(_1uO.b)!=_1sz){return new F(function(){return _1uE(_1uM);});}else{var _1uP=u_iswlower(E(_1uN.b));if(!E(_1uP)){return false;}else{return new F(function(){return _1uE(_1uM);});}}}})(_dC,_dD))){var _1uQ=function(_1uR){while(1){var _1uS=B((function(_1uT){var _1uU=E(_1uT);if(!_1uU._){return E(_1qZ);}else{var _1uV=_1uU.b,_1uW=E(_1uU.a),_1uX=_1r7+E(_1uW.a)|0;if(_1uX<1){_1uR=_1uV;return __continue;}else{if(_1uX>8){_1uR=_1uV;return __continue;}else{var _1uY=_1sy+E(_1uW.b)|0;if(_1uY<1){_1uR=_1uV;return __continue;}else{if(_1uY>8){_1uR=_1uV;return __continue;}else{var _1uZ=B(_4i(_1r7,_1sy,_1uX,_1uY));if(!_1uZ._){return E(_cr);}else{var _1v0=E(_1uZ.b);if(!_1v0._){return E(_8I);}else{if(!B(_1kX(B(_8D(_1v0.a,_1v0.b))))){_1uR=_1uV;return __continue;}else{var _1v1=function(_1v2){while(1){var _1v3=E(_1v2);if(!_1v3._){return true;}else{var _1v4=_1v3.b,_1v5=E(_1v3.a),_1v6=E(_1v5.a);if(E(_1v6.a)!=_1uX){_1v2=_1v4;continue;}else{if(E(_1v6.b)!=_1uY){_1v2=_1v4;continue;}else{var _1v7=u_iswlower(E(_1v5.b));if(!E(_1v7)){return false;}else{_1v2=_1v4;continue;}}}}}};if(!B((function(_1v8,_1v9){var _1va=E(_1v8),_1vb=E(_1va.a);if(E(_1vb.a)!=_1uX){return new F(function(){return _1v1(_1v9);});}else{if(E(_1vb.b)!=_1uY){return new F(function(){return _1v1(_1v9);});}else{var _1vc=u_iswlower(E(_1va.b));if(!E(_1vc)){return false;}else{return new F(function(){return _1v1(_1v9);});}}}})(_dC,_dD))){_1uR=_1uV;return __continue;}else{var _1vd=new T(function(){var _1ve=function(_1vf){while(1){var _1vg=E(_1vf);if(!_1vg._){return false;}else{var _1vh=_1vg.b,_1vi=E(E(_1vg.a).a);if(E(_1vi.a)!=_1uX){_1vf=_1vh;continue;}else{if(E(_1vi.b)!=_1uY){_1vf=_1vh;continue;}else{return true;}}}}};if(!B((function(_1vj,_1vk){var _1vl=E(E(_1vj).a);if(E(_1vl.a)!=_1uX){return new F(function(){return _1ve(_1vk);});}else{if(E(_1vl.b)!=_1uY){return new F(function(){return _1ve(_1vk);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_1vm=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_1uX)==8){if(E(_1uY)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_1uX)==1){if(E(_1uY)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_1r0))));}),_1vn=new T(function(){var _1vo=function(_1vp){var _1vq=E(_1vp),_1vr=E(_1vq.a),_1vs=_1vr.b,_1vt=E(_1vr.a),_1vu=function(_1vv){return (_1vt!=_1r7)?true:(E(_1vs)!=_1sy)?true:(E(_1vq.b)==82)?false:true;};if(_1vt!=_1uX){return new F(function(){return _1vu(_);});}else{if(E(_1vs)!=_1uY){return new F(function(){return _1vu(_);});}else{return false;}}};return B(_5R(_1vo,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1uX,_1uY),_8T),_1vn),b:_5J,c:_1vm,d:_ds,e:_1vd,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_1uQ(_1uV));}));}}}}}}}}}})(_1uR));if(_1uS!=__continue){return _1uS;}}};return new F(function(){return _1uQ(_1r4);});}else{var _1vw=new T(function(){var _1vx=function(_1vy){while(1){var _1vz=B((function(_1vA){var _1vB=E(_1vA);if(!_1vB._){return E(_1qZ);}else{var _1vC=_1vB.b,_1vD=E(_1vB.a),_1vE=_1r7+E(_1vD.a)|0;if(_1vE<1){_1vy=_1vC;return __continue;}else{if(_1vE>8){_1vy=_1vC;return __continue;}else{var _1vF=_1sy+E(_1vD.b)|0;if(_1vF<1){_1vy=_1vC;return __continue;}else{if(_1vF>8){_1vy=_1vC;return __continue;}else{var _1vG=B(_4i(_1r7,_1sy,_1vE,_1vF));if(!_1vG._){return E(_cr);}else{var _1vH=E(_1vG.b);if(!_1vH._){return E(_8I);}else{if(!B(_1kX(B(_8D(_1vH.a,_1vH.b))))){_1vy=_1vC;return __continue;}else{var _1vI=function(_1vJ){while(1){var _1vK=E(_1vJ);if(!_1vK._){return true;}else{var _1vL=_1vK.b,_1vM=E(_1vK.a),_1vN=E(_1vM.a);if(E(_1vN.a)!=_1vE){_1vJ=_1vL;continue;}else{if(E(_1vN.b)!=_1vF){_1vJ=_1vL;continue;}else{var _1vO=u_iswlower(E(_1vM.b));if(!E(_1vO)){return false;}else{_1vJ=_1vL;continue;}}}}}};if(!B((function(_1vP,_1vQ){var _1vR=E(_1vP),_1vS=E(_1vR.a);if(E(_1vS.a)!=_1vE){return new F(function(){return _1vI(_1vQ);});}else{if(E(_1vS.b)!=_1vF){return new F(function(){return _1vI(_1vQ);});}else{var _1vT=u_iswlower(E(_1vR.b));if(!E(_1vT)){return false;}else{return new F(function(){return _1vI(_1vQ);});}}}})(_dC,_dD))){_1vy=_1vC;return __continue;}else{var _1vU=new T(function(){var _1vV=function(_1vW){while(1){var _1vX=E(_1vW);if(!_1vX._){return false;}else{var _1vY=_1vX.b,_1vZ=E(E(_1vX.a).a);if(E(_1vZ.a)!=_1vE){_1vW=_1vY;continue;}else{if(E(_1vZ.b)!=_1vF){_1vW=_1vY;continue;}else{return true;}}}}};if(!B((function(_1w0,_1w1){var _1w2=E(E(_1w0).a);if(E(_1w2.a)!=_1vE){return new F(function(){return _1vV(_1w1);});}else{if(E(_1w2.b)!=_1vF){return new F(function(){return _1vV(_1w1);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_1w3=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_1vE)==8){if(E(_1vF)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_1vE)==1){if(E(_1vF)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_1r0))));}),_1w4=new T(function(){var _1w5=function(_1w6){var _1w7=E(_1w6),_1w8=E(_1w7.a),_1w9=_1w8.b,_1wa=E(_1w8.a),_1wb=function(_1wc){return (_1wa!=_1r7)?true:(E(_1w9)!=_1sy)?true:(E(_1w7.b)==82)?false:true;};if(_1wa!=_1vE){return new F(function(){return _1wb(_);});}else{if(E(_1w9)!=_1vF){return new F(function(){return _1wb(_);});}else{return false;}}};return B(_5R(_1w5,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1vE,_1vF),_8T),_1w4),b:_5J,c:_1w3,d:_ds,e:_1vU,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_1vx(_1vC));}));}}}}}}}}}})(_1vy));if(_1vz!=__continue){return _1vz;}}};return B(_1vx(_1r4));}),_1wd=new T(function(){var _1we=function(_1wf){while(1){var _1wg=E(_1wf);if(!_1wg._){return false;}else{var _1wh=_1wg.b,_1wi=E(E(_1wg.a).a);if(E(_1wi.a)!=_1r9){_1wf=_1wh;continue;}else{if(E(_1wi.b)!=_1sz){_1wf=_1wh;continue;}else{return true;}}}}};if(!B((function(_1wj,_1wk){var _1wl=E(E(_1wj).a);if(E(_1wl.a)!=_1r9){return new F(function(){return _1we(_1wk);});}else{if(E(_1wl.b)!=_1sz){return new F(function(){return _1we(_1wk);});}else{return true;}}})(_dC,_dD))){return E(_8M);}else{return E(_8U);}}),_1wm=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_1r9)==8){if(E(_1sz)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_1r9)==1){if(E(_1sz)==8){return true;}else{return false;}}else{return false;}}else{return true;}}),_1r0))));}),_1wn=new T(function(){var _1wo=function(_1wp){var _1wq=E(_1wp),_1wr=E(_1wq.a),_1ws=_1wr.b,_1wt=E(_1wr.a),_1wu=function(_1wv){return (_1wt!=_1r7)?true:(E(_1ws)!=_1sy)?true:(E(_1wq.b)==82)?false:true;};if(_1wt!=_1r9){return new F(function(){return _1wu(_);});}else{if(E(_1ws)!=_1sz){return new F(function(){return _1wu(_);});}else{return false;}}};return B(_5R(_1wo,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1r9,_1sz),_8T),_1wn),b:_5J,c:_1wm,d:_ds,e:_1wd,f:_8S,g:_8L,h:_8L,i:_5K},_1vw);}}}}}}}}}}else{return E(_1qZ);}};return B(_1qU(_dC,_dD));}),_1ww=function(_1wx){while(1){var _1wy=B((function(_1wz){var _1wA=E(_1wz);if(!_1wA._){return E(_VG);}else{var _1wB=_1wA.b,_1wC=E(_1wA.a),_1wD=_1wC.a;if(E(_1wC.b)==80){var _1wE=new T(function(){return E(E(_1wD).b)+1|0;}),_1wF=function(_1wG,_1wH){var _1wI=E(_du),_1wJ=E(_1wD),_1wK=E(_1wJ.a),_1wL=_1wK+_1wG|0;if(_1wL!=E(_1wI.a)){return E(_1wH);}else{var _1wM=E(_1wE);if(_1wM!=E(_1wI.b)){return E(_1wH);}else{var _1wN=new T(function(){var _1wO=function(_1wP){var _1wQ=E(_1wP),_1wR=E(_1wQ.a),_1wS=_1wR.b,_1wT=E(_1wR.a),_1wU=function(_1wV){return (_1wT!=_1wK)?true:(E(_1wS)!=E(_1wJ.b))?true:(E(_1wQ.b)==80)?false:true;};if(_1wT!=_1wL){return new F(function(){return _1wU(_);});}else{if(E(_1wS)!=(_1wM-1|0)){return new F(function(){return _1wU(_);});}else{return false;}}};return B(_5R(_1wO,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1wL,_1wM),_aL),_1wN),b:_5J,c:_dr,d:_ds,e:_8U,f:_8S,g:_8L,h:_8L,i:_5K},_1wH);}}},_1wW=new T(function(){return B(_1wF(1,new T(function(){return B(_1ww(_1wB));})));});return new F(function(){return _1wF(-1,_1wW);});}else{_1wx=_1wB;return __continue;}}})(_1wx));if(_1wy!=__continue){return _1wy;}}},_1wX=function(_1wY,_1wZ){var _1x0=E(_1wY),_1x1=_1x0.a;if(E(_1x0.b)==80){var _1x2=new T(function(){return E(E(_1x1).b)+1|0;}),_1x3=function(_1x4,_1x5){var _1x6=E(_du),_1x7=E(_1x1),_1x8=E(_1x7.a),_1x9=_1x8+_1x4|0;if(_1x9!=E(_1x6.a)){return E(_1x5);}else{var _1xa=E(_1x2);if(_1xa!=E(_1x6.b)){return E(_1x5);}else{var _1xb=new T(function(){var _1xc=function(_1xd){var _1xe=E(_1xd),_1xf=E(_1xe.a),_1xg=_1xf.b,_1xh=E(_1xf.a),_1xi=function(_1xj){return (_1xh!=_1x8)?true:(E(_1xg)!=E(_1x7.b))?true:(E(_1xe.b)==80)?false:true;};if(_1xh!=_1x9){return new F(function(){return _1xi(_);});}else{if(E(_1xg)!=(_1xa-1|0)){return new F(function(){return _1xi(_);});}else{return false;}}};return B(_5R(_1xc,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1x9,_1xa),_aL),_1xb),b:_5J,c:_dr,d:_ds,e:_8U,f:_8S,g:_8L,h:_8L,i:_5K},_1x5);}}},_1xk=new T(function(){return B(_1x3(1,new T(function(){return B(_1ww(_1wZ));})));});return new F(function(){return _1x3(-1,_1xk);});}else{return new F(function(){return _1ww(_1wZ);});}};return B(_1wX(_dC,_dD));}),_1xl=function(_1xm){while(1){var _1xn=B((function(_1xo){var _1xp=E(_1xo);if(!_1xp._){return E(_VF);}else{var _1xq=_1xp.b,_1xr=E(_1xp.a),_1xs=_1xr.a;if(E(_1xr.b)==80){var _1xt=new T(function(){return E(E(_1xs).b)+1|0;}),_1xu=function(_1xv,_1xw){var _1xx=E(_1xs),_1xy=_1xx.b,_1xz=E(_1xx.a),_1xA=_1xz+_1xv|0;if(_1xA<1){return E(_1xw);}else{if(_1xA>8){return E(_1xw);}else{var _1xB=E(_1xt);if(_1xB<1){return E(_1xw);}else{if(_1xB>8){return E(_1xw);}else{var _1xC=function(_1xD){while(1){var _1xE=E(_1xD);if(!_1xE._){return false;}else{var _1xF=_1xE.b,_1xG=E(_1xE.a),_1xH=E(_1xG.a);if(E(_1xH.a)!=_1xA){_1xD=_1xF;continue;}else{if(E(_1xH.b)!=_1xB){_1xD=_1xF;continue;}else{var _1xI=u_iswlower(E(_1xG.b));if(!E(_1xI)){_1xD=_1xF;continue;}else{return true;}}}}}};if(!B((function(_1xJ,_1xK){var _1xL=E(_1xJ),_1xM=E(_1xL.a);if(E(_1xM.a)!=_1xA){return new F(function(){return _1xC(_1xK);});}else{if(E(_1xM.b)!=_1xB){return new F(function(){return _1xC(_1xK);});}else{var _1xN=u_iswlower(E(_1xL.b));if(!E(_1xN)){return new F(function(){return _1xC(_1xK);});}else{return true;}}}})(_dC,_dD))){return E(_1xw);}else{var _1xO=new T2(0,_1xA,_1xB),_1xP=E(_1xB);if(_1xP==8){var _1xQ=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_1xA)==8){return true;}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_1xA)==1){return true;}else{return false;}}else{return true;}}),_dr))));}),_1xR=new T(function(){var _1xS=function(_1xT){var _1xU=E(_1xT),_1xV=E(_1xU.a),_1xW=_1xV.b,_1xX=E(_1xV.a),_1xY=function(_1xZ){return (_1xX!=_1xz)?true:(E(_1xW)!=E(_1xy))?true:(E(_1xU.b)==80)?false:true;};if(_1xX!=_1xA){return new F(function(){return _1xY(_);});}else{if(E(_1xW)==8){return false;}else{return new F(function(){return _1xY(_);});}}};return B(_5R(_1xS,_dB));}),_1y0=new T(function(){var _1y1=function(_1y2){var _1y3=E(_1y2),_1y4=E(_1y3.a),_1y5=_1y4.b,_1y6=E(_1y4.a),_1y7=function(_1y8){return (_1y6!=_1xz)?true:(E(_1y5)!=E(_1xy))?true:(E(_1y3.b)==80)?false:true;};if(_1y6!=_1xA){return new F(function(){return _1y7(_);});}else{if(E(_1y5)==8){return false;}else{return new F(function(){return _1y7(_);});}}};return B(_5R(_1y1,_dB));}),_1y9=new T(function(){var _1ya=function(_1yb){var _1yc=E(_1yb),_1yd=E(_1yc.a),_1ye=_1yd.b,_1yf=E(_1yd.a),_1yg=function(_1yh){return (_1yf!=_1xz)?true:(E(_1ye)!=E(_1xy))?true:(E(_1yc.b)==80)?false:true;};if(_1yf!=_1xA){return new F(function(){return _1yg(_);});}else{if(E(_1ye)==8){return false;}else{return new F(function(){return _1yg(_);});}}};return B(_5R(_1ya,_dB));}),_1yi=new T(function(){var _1yj=function(_1yk){var _1yl=E(_1yk),_1ym=E(_1yl.a),_1yn=_1ym.b,_1yo=E(_1ym.a),_1yp=function(_1yq){return (_1yo!=_1xz)?true:(E(_1yn)!=E(_1xy))?true:(E(_1yl.b)==80)?false:true;};if(_1yo!=_1xA){return new F(function(){return _1yp(_);});}else{if(E(_1yn)==8){return false;}else{return new F(function(){return _1yp(_);});}}};return B(_5R(_1yj,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,_1xO,_9Z),_1yi),b:_5J,c:_1xQ,d:_ds,e:_8U,f:_8S,g:_8L,h:_8L,i:_5K},new T2(1,{_:0,a:new T2(1,new T2(0,_1xO,_8T),_1y9),b:_5J,c:_1xQ,d:_ds,e:_8M,f:_8S,g:_8L,h:_8L,i:_5K},new T2(1,{_:0,a:new T2(1,new T2(0,_1xO,_aj),_1y0),b:_5J,c:_1xQ,d:_ds,e:_8M,f:_8S,g:_8L,h:_8L,i:_5K},new T2(1,{_:0,a:new T2(1,new T2(0,_1xO,_a0),_1xR),b:_5J,c:_1xQ,d:_ds,e:_8M,f:_8S,g:_8L,h:_8L,i:_5K},_1xw))));}else{var _1yr=new T(function(){var _1ys=function(_1yt){var _1yu=E(_1yt),_1yv=E(_1yu.a),_1yw=_1yv.b,_1yx=E(_1yv.a),_1yy=function(_1yz){return (_1yx!=_1xz)?true:(E(_1yw)!=E(_1xy))?true:(E(_1yu.b)==80)?false:true;};if(_1yx!=_1xA){return new F(function(){return _1yy(_);});}else{if(E(_1yw)!=_1xP){return new F(function(){return _1yy(_);});}else{return false;}}};return B(_5R(_1ys,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,_1xO,_aL),_1yr),b:_5J,c:_dr,d:_ds,e:_8U,f:_8S,g:_8L,h:_8L,i:_5K},_1xw);}}}}}}},_1yA=new T(function(){return B(_1xu(1,new T(function(){return B(_1xl(_1xq));})));});return new F(function(){return _1xu(-1,_1yA);});}else{_1xm=_1xq;return __continue;}}})(_1xm));if(_1xn!=__continue){return _1xn;}}},_1yB=function(_1yC,_1yD){var _1yE=E(_1yC),_1yF=_1yE.a;if(E(_1yE.b)==80){var _1yG=new T(function(){return E(E(_1yF).b)+1|0;}),_1yH=function(_1yI,_1yJ){var _1yK=E(_1yF),_1yL=_1yK.b,_1yM=E(_1yK.a),_1yN=_1yM+_1yI|0;if(_1yN<1){return E(_1yJ);}else{if(_1yN>8){return E(_1yJ);}else{var _1yO=E(_1yG);if(_1yO<1){return E(_1yJ);}else{if(_1yO>8){return E(_1yJ);}else{var _1yP=function(_1yQ){while(1){var _1yR=E(_1yQ);if(!_1yR._){return false;}else{var _1yS=_1yR.b,_1yT=E(_1yR.a),_1yU=E(_1yT.a);if(E(_1yU.a)!=_1yN){_1yQ=_1yS;continue;}else{if(E(_1yU.b)!=_1yO){_1yQ=_1yS;continue;}else{var _1yV=u_iswlower(E(_1yT.b));if(!E(_1yV)){_1yQ=_1yS;continue;}else{return true;}}}}}};if(!B((function(_1yW,_1yX){var _1yY=E(_1yW),_1yZ=E(_1yY.a);if(E(_1yZ.a)!=_1yN){return new F(function(){return _1yP(_1yX);});}else{if(E(_1yZ.b)!=_1yO){return new F(function(){return _1yP(_1yX);});}else{var _1z0=u_iswlower(E(_1yY.b));if(!E(_1z0)){return new F(function(){return _1yP(_1yX);});}else{return true;}}}})(_dC,_dD))){return E(_1yJ);}else{var _1z1=new T2(0,_1yN,_1yO),_1z2=E(_1yO);if(_1z2==8){var _1z3=new T(function(){return B(_5B(2,new T(function(){if(!E(_dy)){if(E(_1yN)==8){return true;}else{return false;}}else{return true;}}),B(_5B(3,new T(function(){if(!E(_dx)){if(E(_1yN)==1){return true;}else{return false;}}else{return true;}}),_dr))));}),_1z4=new T(function(){var _1z5=function(_1z6){var _1z7=E(_1z6),_1z8=E(_1z7.a),_1z9=_1z8.b,_1za=E(_1z8.a),_1zb=function(_1zc){return (_1za!=_1yM)?true:(E(_1z9)!=E(_1yL))?true:(E(_1z7.b)==80)?false:true;};if(_1za!=_1yN){return new F(function(){return _1zb(_);});}else{if(E(_1z9)==8){return false;}else{return new F(function(){return _1zb(_);});}}};return B(_5R(_1z5,_dB));}),_1zd=new T(function(){var _1ze=function(_1zf){var _1zg=E(_1zf),_1zh=E(_1zg.a),_1zi=_1zh.b,_1zj=E(_1zh.a),_1zk=function(_1zl){return (_1zj!=_1yM)?true:(E(_1zi)!=E(_1yL))?true:(E(_1zg.b)==80)?false:true;};if(_1zj!=_1yN){return new F(function(){return _1zk(_);});}else{if(E(_1zi)==8){return false;}else{return new F(function(){return _1zk(_);});}}};return B(_5R(_1ze,_dB));}),_1zm=new T(function(){var _1zn=function(_1zo){var _1zp=E(_1zo),_1zq=E(_1zp.a),_1zr=_1zq.b,_1zs=E(_1zq.a),_1zt=function(_1zu){return (_1zs!=_1yM)?true:(E(_1zr)!=E(_1yL))?true:(E(_1zp.b)==80)?false:true;};if(_1zs!=_1yN){return new F(function(){return _1zt(_);});}else{if(E(_1zr)==8){return false;}else{return new F(function(){return _1zt(_);});}}};return B(_5R(_1zn,_dB));}),_1zv=new T(function(){var _1zw=function(_1zx){var _1zy=E(_1zx),_1zz=E(_1zy.a),_1zA=_1zz.b,_1zB=E(_1zz.a),_1zC=function(_1zD){return (_1zB!=_1yM)?true:(E(_1zA)!=E(_1yL))?true:(E(_1zy.b)==80)?false:true;};if(_1zB!=_1yN){return new F(function(){return _1zC(_);});}else{if(E(_1zA)==8){return false;}else{return new F(function(){return _1zC(_);});}}};return B(_5R(_1zw,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,_1z1,_9Z),_1zv),b:_5J,c:_1z3,d:_ds,e:_8U,f:_8S,g:_8L,h:_8L,i:_5K},new T2(1,{_:0,a:new T2(1,new T2(0,_1z1,_8T),_1zm),b:_5J,c:_1z3,d:_ds,e:_8M,f:_8S,g:_8L,h:_8L,i:_5K},new T2(1,{_:0,a:new T2(1,new T2(0,_1z1,_aj),_1zd),b:_5J,c:_1z3,d:_ds,e:_8M,f:_8S,g:_8L,h:_8L,i:_5K},new T2(1,{_:0,a:new T2(1,new T2(0,_1z1,_a0),_1z4),b:_5J,c:_1z3,d:_ds,e:_8M,f:_8S,g:_8L,h:_8L,i:_5K},_1yJ))));}else{var _1zE=new T(function(){var _1zF=function(_1zG){var _1zH=E(_1zG),_1zI=E(_1zH.a),_1zJ=_1zI.b,_1zK=E(_1zI.a),_1zL=function(_1zM){return (_1zK!=_1yM)?true:(E(_1zJ)!=E(_1yL))?true:(E(_1zH.b)==80)?false:true;};if(_1zK!=_1yN){return new F(function(){return _1zL(_);});}else{if(E(_1zJ)!=_1z2){return new F(function(){return _1zL(_);});}else{return false;}}};return B(_5R(_1zF,_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,_1z1,_aL),_1zE),b:_5J,c:_dr,d:_ds,e:_8U,f:_8S,g:_8L,h:_8L,i:_5K},_1yJ);}}}}}}},_1zN=new T(function(){return B(_1yH(1,new T(function(){return B(_1xl(_1yD));})));});return new F(function(){return _1yH(-1,_1zN);});}else{return new F(function(){return _1xl(_1yD);});}};return B(_1yB(_dC,_dD));}),_1zO=function(_1zP){while(1){var _1zQ=B((function(_1zR){var _1zS=E(_1zR);if(!_1zS._){return E(_VE);}else{var _1zT=_1zS.b,_1zU=E(_1zS.a);if(E(_1zU.b)==80){var _1zV=E(_1zU.a);if(E(_1zV.b)==2){var _1zW=E(E(_dC).a),_1zX=_1zW.b,_1zY=E(_1zW.a),_1zZ=E(_1zV.a),_1A0=function(_1A1){if(_1zY!=_1zZ){var _1A2=function(_1A3){var _1A4=E(_1A3);if(!_1A4._){return true;}else{var _1A5=_1A4.b,_1A6=E(E(_1A4.a).a),_1A7=_1A6.b,_1A8=E(_1A6.a),_1A9=function(_1Aa){if(_1A8!=_1zZ){return new F(function(){return _1A2(_1A5);});}else{if(E(_1A7)==3){return false;}else{return new F(function(){return _1A2(_1A5);});}}};if(_1A8!=_1zZ){return new F(function(){return _1A9(_);});}else{if(E(_1A7)==4){return false;}else{return new F(function(){return _1A9(_);});}}}};return new F(function(){return _1A2(_dD);});}else{if(E(_1zX)==3){return false;}else{var _1Ab=function(_1Ac){var _1Ad=E(_1Ac);if(!_1Ad._){return true;}else{var _1Ae=_1Ad.b,_1Af=E(E(_1Ad.a).a),_1Ag=_1Af.b,_1Ah=E(_1Af.a),_1Ai=function(_1Aj){if(_1Ah!=_1zZ){return new F(function(){return _1Ab(_1Ae);});}else{if(E(_1Ag)==3){return false;}else{return new F(function(){return _1Ab(_1Ae);});}}};if(_1Ah!=_1zZ){return new F(function(){return _1Ai(_);});}else{if(E(_1Ag)==4){return false;}else{return new F(function(){return _1Ai(_);});}}}};return new F(function(){return _1Ab(_dD);});}}},_1Ak=function(_1Al){var _1Am=new T(function(){return B(_5R(function(_1An){var _1Ao=E(_1An),_1Ap=E(_1Ao.a);return (E(_1Ap.a)!=_1zZ)?true:(E(_1Ap.b)==2)?(E(_1Ao.b)==80)?false:true:true;},_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1zZ,_8O),_aL),_1Am),b:_5J,c:_dr,d:_ds,e:_8M,f:new T2(0,_1zZ,_8N),g:_8L,h:_8L,i:_5K},new T(function(){return B(_1zO(_1zT));}));};if(_1zY!=_1zZ){if(!B(_1A0(_))){_1zP=_1zT;return __continue;}else{return new F(function(){return _1Ak(_);});}}else{if(E(_1zX)==4){_1zP=_1zT;return __continue;}else{if(!B(_1A0(_))){_1zP=_1zT;return __continue;}else{return new F(function(){return _1Ak(_);});}}}}else{_1zP=_1zT;return __continue;}}else{_1zP=_1zT;return __continue;}}})(_1zP));if(_1zQ!=__continue){return _1zQ;}}},_1Aq=function(_1Ar,_1As){var _1At=E(_1Ar);if(E(_1At.b)==80){var _1Au=E(_1At.a);if(E(_1Au.b)==2){var _1Av=E(E(_dC).a),_1Aw=_1Av.b,_1Ax=E(_1Av.a),_1Ay=E(_1Au.a),_1Az=function(_1AA){if(_1Ax!=_1Ay){var _1AB=function(_1AC){var _1AD=E(_1AC);if(!_1AD._){return true;}else{var _1AE=_1AD.b,_1AF=E(E(_1AD.a).a),_1AG=_1AF.b,_1AH=E(_1AF.a),_1AI=function(_1AJ){if(_1AH!=_1Ay){return new F(function(){return _1AB(_1AE);});}else{if(E(_1AG)==3){return false;}else{return new F(function(){return _1AB(_1AE);});}}};if(_1AH!=_1Ay){return new F(function(){return _1AI(_);});}else{if(E(_1AG)==4){return false;}else{return new F(function(){return _1AI(_);});}}}};return new F(function(){return _1AB(_dD);});}else{if(E(_1Aw)==3){return false;}else{var _1AK=function(_1AL){var _1AM=E(_1AL);if(!_1AM._){return true;}else{var _1AN=_1AM.b,_1AO=E(E(_1AM.a).a),_1AP=_1AO.b,_1AQ=E(_1AO.a),_1AR=function(_1AS){if(_1AQ!=_1Ay){return new F(function(){return _1AK(_1AN);});}else{if(E(_1AP)==3){return false;}else{return new F(function(){return _1AK(_1AN);});}}};if(_1AQ!=_1Ay){return new F(function(){return _1AR(_);});}else{if(E(_1AP)==4){return false;}else{return new F(function(){return _1AR(_);});}}}};return new F(function(){return _1AK(_dD);});}}},_1AT=function(_1AU){var _1AV=new T(function(){return B(_5R(function(_1AW){var _1AX=E(_1AW),_1AY=E(_1AX.a);return (E(_1AY.a)!=_1Ay)?true:(E(_1AY.b)==2)?(E(_1AX.b)==80)?false:true:true;},_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,new T2(0,_1Ay,_8O),_aL),_1AV),b:_5J,c:_dr,d:_ds,e:_8M,f:new T2(0,_1Ay,_8N),g:_8L,h:_8L,i:_5K},new T(function(){return B(_1zO(_1As));}));};if(_1Ax!=_1Ay){if(!B(_1Az(_))){return new F(function(){return _1zO(_1As);});}else{return new F(function(){return _1AT(_);});}}else{if(E(_1Aw)==4){return new F(function(){return _1zO(_1As);});}else{if(!B(_1Az(_))){return new F(function(){return _1zO(_1As);});}else{return new F(function(){return _1AT(_);});}}}}else{return new F(function(){return _1zO(_1As);});}}else{return new F(function(){return _1zO(_1As);});}};return B(_1Aq(_dC,_dD));}),_1AZ=function(_1B0){while(1){var _1B1=B((function(_1B2){var _1B3=E(_1B2);if(!_1B3._){return E(_VD);}else{var _1B4=_1B3.b,_1B5=E(_1B3.a),_1B6=_1B5.a;if(E(_1B5.b)==80){var _1B7=new T(function(){return E(E(_1B6).b)+1|0;}),_1B8=E(E(_dC).a),_1B9=E(_1B6),_1Ba=_1B9.b,_1Bb=E(_1B9.a),_1Bc=function(_1Bd){var _1Be=E(_1B7),_1Bf=new T2(0,_1Bb,_1Be);if(E(_1Be)==8){var _1Bg=new T(function(){return B(_5R(function(_1Bh){var _1Bi=E(_1Bh),_1Bj=E(_1Bi.a);return (E(_1Bj.a)!=_1Bb)?true:(E(_1Bj.b)!=E(_1Ba))?true:(E(_1Bi.b)==80)?false:true;},_dB));}),_1Bk=new T(function(){return B(_5R(function(_1Bl){var _1Bm=E(_1Bl),_1Bn=E(_1Bm.a);return (E(_1Bn.a)!=_1Bb)?true:(E(_1Bn.b)!=E(_1Ba))?true:(E(_1Bm.b)==80)?false:true;},_dB));}),_1Bo=new T(function(){return B(_5R(function(_1Bp){var _1Bq=E(_1Bp),_1Br=E(_1Bq.a);return (E(_1Br.a)!=_1Bb)?true:(E(_1Br.b)!=E(_1Ba))?true:(E(_1Bq.b)==80)?false:true;},_dB));}),_1Bs=new T(function(){return B(_5R(function(_1Bt){var _1Bu=E(_1Bt),_1Bv=E(_1Bu.a);return (E(_1Bv.a)!=_1Bb)?true:(E(_1Bv.b)!=E(_1Ba))?true:(E(_1Bu.b)==80)?false:true;},_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,_1Bf,_9Z),_1Bs),b:_5J,c:_dr,d:_ds,e:_8U,f:_8S,g:_8L,h:_8L,i:_5K},new T2(1,{_:0,a:new T2(1,new T2(0,_1Bf,_8T),_1Bo),b:_5J,c:_dr,d:_ds,e:_8M,f:_8S,g:_8L,h:_8L,i:_5K},new T2(1,{_:0,a:new T2(1,new T2(0,_1Bf,_aj),_1Bk),b:_5J,c:_dr,d:_ds,e:_8M,f:_8S,g:_8L,h:_8L,i:_5K},new T2(1,{_:0,a:new T2(1,new T2(0,_1Bf,_a0),_1Bg),b:_5J,c:_dr,d:_ds,e:_8M,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_1AZ(_1B4));})))));}else{var _1Bw=new T(function(){return B(_5R(function(_1Bx){var _1By=E(_1Bx),_1Bz=E(_1By.a);return (E(_1Bz.a)!=_1Bb)?true:(E(_1Bz.b)!=E(_1Ba))?true:(E(_1By.b)==80)?false:true;},_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,_1Bf,_aL),_1Bw),b:_5J,c:_dr,d:_ds,e:_8M,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_1AZ(_1B4));}));}};if(E(_1B8.a)!=_1Bb){var _1BA=function(_1BB){while(1){var _1BC=E(_1BB);if(!_1BC._){return true;}else{var _1BD=_1BC.b,_1BE=E(E(_1BC.a).a);if(E(_1BE.a)!=_1Bb){_1BB=_1BD;continue;}else{if(E(_1BE.b)!=E(_1B7)){_1BB=_1BD;continue;}else{return false;}}}}};if(!B(_1BA(_dD))){_1B0=_1B4;return __continue;}else{return new F(function(){return _1Bc(_);});}}else{var _1BF=E(_1B7);if(E(_1B8.b)!=_1BF){var _1BG=function(_1BH){while(1){var _1BI=E(_1BH);if(!_1BI._){return true;}else{var _1BJ=_1BI.b,_1BK=E(E(_1BI.a).a);if(E(_1BK.a)!=_1Bb){_1BH=_1BJ;continue;}else{if(E(_1BK.b)!=_1BF){_1BH=_1BJ;continue;}else{return false;}}}}};if(!B(_1BG(_dD))){_1B0=_1B4;return __continue;}else{return new F(function(){return _1Bc(_);});}}else{_1B0=_1B4;return __continue;}}}else{_1B0=_1B4;return __continue;}}})(_1B0));if(_1B1!=__continue){return _1B1;}}},_1BL=function(_1BM,_1BN){var _1BO=E(_1BM),_1BP=_1BO.a;if(E(_1BO.b)==80){var _1BQ=new T(function(){return E(E(_1BP).b)+1|0;}),_1BR=E(E(_dC).a),_1BS=E(_1BP),_1BT=_1BS.b,_1BU=E(_1BS.a),_1BV=function(_1BW){var _1BX=E(_1BQ),_1BY=new T2(0,_1BU,_1BX);if(E(_1BX)==8){var _1BZ=new T(function(){return B(_5R(function(_1C0){var _1C1=E(_1C0),_1C2=E(_1C1.a);return (E(_1C2.a)!=_1BU)?true:(E(_1C2.b)!=E(_1BT))?true:(E(_1C1.b)==80)?false:true;},_dB));}),_1C3=new T(function(){return B(_5R(function(_1C4){var _1C5=E(_1C4),_1C6=E(_1C5.a);return (E(_1C6.a)!=_1BU)?true:(E(_1C6.b)!=E(_1BT))?true:(E(_1C5.b)==80)?false:true;},_dB));}),_1C7=new T(function(){return B(_5R(function(_1C8){var _1C9=E(_1C8),_1Ca=E(_1C9.a);return (E(_1Ca.a)!=_1BU)?true:(E(_1Ca.b)!=E(_1BT))?true:(E(_1C9.b)==80)?false:true;},_dB));}),_1Cb=new T(function(){return B(_5R(function(_1Cc){var _1Cd=E(_1Cc),_1Ce=E(_1Cd.a);return (E(_1Ce.a)!=_1BU)?true:(E(_1Ce.b)!=E(_1BT))?true:(E(_1Cd.b)==80)?false:true;},_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,_1BY,_9Z),_1Cb),b:_5J,c:_dr,d:_ds,e:_8U,f:_8S,g:_8L,h:_8L,i:_5K},new T2(1,{_:0,a:new T2(1,new T2(0,_1BY,_8T),_1C7),b:_5J,c:_dr,d:_ds,e:_8M,f:_8S,g:_8L,h:_8L,i:_5K},new T2(1,{_:0,a:new T2(1,new T2(0,_1BY,_aj),_1C3),b:_5J,c:_dr,d:_ds,e:_8M,f:_8S,g:_8L,h:_8L,i:_5K},new T2(1,{_:0,a:new T2(1,new T2(0,_1BY,_a0),_1BZ),b:_5J,c:_dr,d:_ds,e:_8M,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_1AZ(_1BN));})))));}else{var _1Cf=new T(function(){return B(_5R(function(_1Cg){var _1Ch=E(_1Cg),_1Ci=E(_1Ch.a);return (E(_1Ci.a)!=_1BU)?true:(E(_1Ci.b)!=E(_1BT))?true:(E(_1Ch.b)==80)?false:true;},_dB));});return new T2(1,{_:0,a:new T2(1,new T2(0,_1BY,_aL),_1Cf),b:_5J,c:_dr,d:_ds,e:_8M,f:_8S,g:_8L,h:_8L,i:_5K},new T(function(){return B(_1AZ(_1BN));}));}};if(E(_1BR.a)!=_1BU){var _1Cj=function(_1Ck){while(1){var _1Cl=E(_1Ck);if(!_1Cl._){return true;}else{var _1Cm=_1Cl.b,_1Cn=E(E(_1Cl.a).a);if(E(_1Cn.a)!=_1BU){_1Ck=_1Cm;continue;}else{if(E(_1Cn.b)!=E(_1BQ)){_1Ck=_1Cm;continue;}else{return false;}}}}};if(!B(_1Cj(_dD))){return new F(function(){return _1AZ(_1BN);});}else{return new F(function(){return _1BV(_);});}}else{var _1Co=E(_1BQ);if(E(_1BR.b)!=_1Co){var _1Cp=function(_1Cq){while(1){var _1Cr=E(_1Cq);if(!_1Cr._){return true;}else{var _1Cs=_1Cr.b,_1Ct=E(E(_1Cr.a).a);if(E(_1Ct.a)!=_1BU){_1Cq=_1Cs;continue;}else{if(E(_1Ct.b)!=_1Co){_1Cq=_1Cs;continue;}else{return false;}}}}};if(!B(_1Cp(_dD))){return new F(function(){return _1AZ(_1BN);});}else{return new F(function(){return _1BV(_);});}}else{return new F(function(){return _1AZ(_1BN);});}}}else{return new F(function(){return _1AZ(_1BN);});}},_VC=B(_1BL(_dC,_dD));}var _1Cu=function(_1Cv){var _1Cw=new T(function(){var _1Cx=new T(function(){return B(_ct(function(_1Cy,_1Cz){var _1CA=E(E(_1Cy).g),_1CB=E(E(_1Cz).g);return (_1CA<=_1CB)?(_1CA>=_1CB)?1:(!E(_dq))?0:2:(!E(_dq))?2:0;},B(_ck(_8z,_VC))));}),_1CC=new T(function(){return (E(_dn)-5.0000000000000044e-2*E(_dv))/0.95;}),_1CD=new T(function(){return E(_1CC)-1.0e-5;}),_1CE=new T(function(){return (E(_do)-5.0000000000000044e-2*E(_dv))/0.95;}),_1CF=new T(function(){return E(_1CE)+1.0e-5;}),_1CG=function(_1CH,_1CI){var _1CJ=E(_1CI);if(!_1CJ._){return __Z;}else{var _1CK=_1CJ.a,_1CL=_1CJ.b;if(!E(_dq)){var _1CM=E(_1CH),_1CN=E(_1CD);if(_1CM>=_1CN){var _1CO=new T(function(){var _1CP=E(_1CK),_1CQ=E(_1CP.e),_1CR=B(_dk(_dl-_1CQ|0,_ds,_1CC,_1CM,_1CP.a,_1CP.b,_1CP.c,_1CP.d,_1CQ,_1CP.f,_1CP.g,_1CP.i));return {_:0,a:_1CR.a,b:_1CR.b,c:_1CR.c,d:_1CR.d,e:_1CR.e,f:_1CR.f,g:_1CR.g,h:_1CR.h,i:_1CR.i};}),_1CS=new T(function(){var _1CT=function(_1CU,_1CV){var _1CW=E(_1CV);if(!_1CW._){return __Z;}else{var _1CX=E(_1CU);if(_1CX>=_1CN){var _1CY=new T(function(){var _1CZ=E(_1CW.a),_1D0=_1CZ.a,_1D1=_1CZ.b,_1D2=_1CZ.c,_1D3=_1CZ.d,_1D4=_1CZ.f,_1D5=_1CZ.g,_1D6=_1CZ.i,_1D7=E(_1CZ.e),_1D8=B(_dk(_dl-_1D7|0,_ds,_1CX,_1CX,_1D0,_1D1,_1D2,_1D3,_1D7,_1D4,_1D5,_1D6)),_1D9=_1D8.a,_1Da=_1D8.b,_1Db=_1D8.c,_1Dc=_1D8.d,_1Dd=_1D8.e,_1De=_1D8.f,_1Df=_1D8.g,_1Dg=_1D8.i,_1Dh=E(_1CC),_1Di=E(_1D8.h);if(_1Dh>=_1Di){return {_:0,a:_1D9,b:_1Da,c:_1Db,d:_1Dc,e:_1Dd,f:_1De,g:_1Df,h:_1Di,i:_1Dg};}else{if(_1Di>=_1CX){return {_:0,a:_1D9,b:_1Da,c:_1Db,d:_1Dc,e:_1Dd,f:_1De,g:_1Df,h:_1Di,i:_1Dg};}else{var _1Dj=B(_dk(_dl-_1D7|0,_ds,_1Dh,_1Di,_1D0,_1D1,_1D2,_1D3,_1D7,_1D4,_1D5,_1D6));return {_:0,a:_1Dj.a,b:_1Dj.b,c:_1Dj.c,d:_1Dj.d,e:_1Dj.e,f:_1Dj.f,g:_1Dj.g,h:_1Dj.h,i:_1Dj.i};}}}),_1Dk=new T(function(){return B(_1CT(new T(function(){var _1Dl=E(E(_1CY).h);if(_1CX>_1Dl){return E(_1Dl);}else{return E(_1CX);}},1),_1CW.b));});return new T2(1,_1CY,_1Dk);}else{return __Z;}}};return B(_1CT(new T(function(){var _1Dm=E(E(_1CO).h);if(_1CM>_1Dm){return E(_1Dm);}else{return E(_1CM);}},1),_1CL));});return new T2(1,_1CO,_1CS);}else{return __Z;}}else{var _1Dn=E(_1CH),_1Do=E(_1CF);if(_1Dn<=_1Do){var _1Dp=new T(function(){var _1Dq=E(_1CK),_1Dr=E(_1Dq.e),_1Ds=B(_dk(_dl-_1Dr|0,_ds,_1Dn,_1CE,_1Dq.a,_1Dq.b,_1Dq.c,_1Dq.d,_1Dr,_1Dq.f,_1Dq.g,_1Dq.i));return {_:0,a:_1Ds.a,b:_1Ds.b,c:_1Ds.c,d:_1Ds.d,e:_1Ds.e,f:_1Ds.f,g:_1Ds.g,h:_1Ds.h,i:_1Ds.i};}),_1Dt=new T(function(){var _1Du=function(_1Dv,_1Dw){var _1Dx=E(_1Dw);if(!_1Dx._){return __Z;}else{var _1Dy=E(_1Dv);if(_1Dy<=_1Do){var _1Dz=new T(function(){var _1DA=E(_1Dx.a),_1DB=_1DA.a,_1DC=_1DA.b,_1DD=_1DA.c,_1DE=_1DA.d,_1DF=_1DA.f,_1DG=_1DA.g,_1DH=_1DA.i,_1DI=E(_1DA.e),_1DJ=B(_dk(_dl-_1DI|0,_ds,_1Dy,_1Dy,_1DB,_1DC,_1DD,_1DE,_1DI,_1DF,_1DG,_1DH)),_1DK=_1DJ.a,_1DL=_1DJ.b,_1DM=_1DJ.c,_1DN=_1DJ.d,_1DO=_1DJ.e,_1DP=_1DJ.f,_1DQ=_1DJ.g,_1DR=_1DJ.i,_1DS=E(_1DJ.h);if(_1Dy>=_1DS){return {_:0,a:_1DK,b:_1DL,c:_1DM,d:_1DN,e:_1DO,f:_1DP,g:_1DQ,h:_1DS,i:_1DR};}else{var _1DT=E(_1CE);if(_1DS>=_1DT){return {_:0,a:_1DK,b:_1DL,c:_1DM,d:_1DN,e:_1DO,f:_1DP,g:_1DQ,h:_1DS,i:_1DR};}else{var _1DU=B(_dk(_dl-_1DI|0,_ds,_1DS,_1DT,_1DB,_1DC,_1DD,_1DE,_1DI,_1DF,_1DG,_1DH));return {_:0,a:_1DU.a,b:_1DU.b,c:_1DU.c,d:_1DU.d,e:_1DU.e,f:_1DU.f,g:_1DU.g,h:_1DU.h,i:_1DU.i};}}}),_1DV=new T(function(){return B(_1Du(new T(function(){var _1DW=E(E(_1Dz).h);if(_1Dy>_1DW){return E(_1Dy);}else{return E(_1DW);}},1),_1Dx.b));});return new T2(1,_1Dz,_1DV);}else{return __Z;}}};return B(_1Du(new T(function(){var _1DX=E(E(_1Dp).h);if(_1Dn>_1DX){return E(_1Dn);}else{return E(_1DX);}},1),_1CL));});return new T2(1,_1Dp,_1Dt);}else{return __Z;}}}},_1DY=E(_dw);if(!_1DY._){var _1DZ=B(_5f(_dq,_2P,new T(function(){if(!E(_dq)){return true;}else{return false;}}),_2P,_2P,_8R,_8S,_8L,new T(function(){if(!E(_dq)){return E(_cj);}else{return E(_ci);}}),_5K,B(_1CG(new T(function(){if(!E(_dq)){return E(_1CE);}else{return E(_1CC);}},1),_1Cx))));return {_:0,a:_1DZ.a,b:_1DZ.b,c:_1DZ.c,d:_1DZ.d,e:_1DZ.e,f:_1DZ.f,g:_1DZ.g,h:_1DZ.h,i:_1DZ.i};}else{var _1E0=E(_1DY.a),_1E1=_1E0.b,_1E2=_1E0.c,_1E3=_1E0.d,_1E4=_1E0.e,_1E5=_1E0.f,_1E6=_1E0.g,_1E7=_1E0.i,_1E8=E(_1E0.a);if(!_1E8._){var _1E9=B(_5f(_dq,_2P,new T(function(){if(!E(_dq)){return true;}else{return false;}}),_2P,_2P,_8R,_8S,_8L,new T(function(){if(!E(_dq)){return E(_cj);}else{return E(_ci);}}),_5K,B(_1CG(new T(function(){if(!E(_dq)){return E(_1CE);}else{return E(_1CC);}},1),_1Cx))));return {_:0,a:_1E9.a,b:_1E9.b,c:_1E9.c,d:_1E9.d,e:_1E9.e,f:_1E9.f,g:_1E9.g,h:_1E9.h,i:_1E9.i};}else{var _1Ea=new T(function(){return B(_5R(function(_1Eb){return (!B(_v(_16,E(_1Eb).a,_1E8)))?true:false;},_1Cx));});if(!E(_dq)){var _1Ec=E(_1CE),_1Ed=E(_1CD);if(_1Ec>=_1Ed){var _1Ee=new T(function(){var _1Ef=E(_1E4),_1Eg=B(_dk(_dl-_1Ef|0,_ds,_1CC,_1Ec,_1E8,_1E1,_1E2,_1E3,_1Ef,_1E5,_1E6,_1E7));return {_:0,a:_1Eg.a,b:_1Eg.b,c:_1Eg.c,d:_1Eg.d,e:_1Eg.e,f:_1Eg.f,g:_1Eg.g,h:_1Eg.h,i:_1Eg.i};}),_1Eh=function(_1Ei,_1Ej){var _1Ek=E(_1Ej);if(!_1Ek._){return __Z;}else{var _1El=E(_1Ei);if(_1El>=_1Ed){var _1Em=new T(function(){var _1En=E(_1Ek.a),_1Eo=_1En.a,_1Ep=_1En.b,_1Eq=_1En.c,_1Er=_1En.d,_1Es=_1En.f,_1Et=_1En.g,_1Eu=_1En.i,_1Ev=E(_1En.e),_1Ew=B(_dk(_dl-_1Ev|0,_ds,_1El,_1El,_1Eo,_1Ep,_1Eq,_1Er,_1Ev,_1Es,_1Et,_1Eu)),_1Ex=_1Ew.a,_1Ey=_1Ew.b,_1Ez=_1Ew.c,_1EA=_1Ew.d,_1EB=_1Ew.e,_1EC=_1Ew.f,_1ED=_1Ew.g,_1EE=_1Ew.i,_1EF=E(_1CC),_1EG=E(_1Ew.h);if(_1EF>=_1EG){return {_:0,a:_1Ex,b:_1Ey,c:_1Ez,d:_1EA,e:_1EB,f:_1EC,g:_1ED,h:_1EG,i:_1EE};}else{if(_1EG>=_1El){return {_:0,a:_1Ex,b:_1Ey,c:_1Ez,d:_1EA,e:_1EB,f:_1EC,g:_1ED,h:_1EG,i:_1EE};}else{var _1EH=B(_dk(_dl-_1Ev|0,_ds,_1EF,_1EG,_1Eo,_1Ep,_1Eq,_1Er,_1Ev,_1Es,_1Et,_1Eu));return {_:0,a:_1EH.a,b:_1EH.b,c:_1EH.c,d:_1EH.d,e:_1EH.e,f:_1EH.f,g:_1EH.g,h:_1EH.h,i:_1EH.i};}}}),_1EI=new T(function(){return B(_1Eh(new T(function(){var _1EJ=E(E(_1Em).h);if(_1El>_1EJ){return E(_1EJ);}else{return E(_1El);}},1),_1Ek.b));});return new T2(1,_1Em,_1EI);}else{return __Z;}}},_1EK=B(_1Eh(new T(function(){var _1EL=E(E(_1Ee).h);if(_1Ec>_1EL){return E(_1EL);}else{return E(_1Ec);}},1),_1Ea)),_1EM=E(_1Ee),_1EN=E(_1EM.h);if(_1EN>=2.1472688986353e9){var _1EO=B(_1m(_2P,_5L,_2P,_2P,_8R,_8S,_8L,2.1472688986353e9,_5K,_1EK));return {_:0,a:_1EO.a,b:_1EO.b,c:_1EO.c,d:_1EO.d,e:_1EO.e,f:_1EO.f,g:_1EO.g,h:_1EO.h,i:_1EO.i};}else{var _1EP=B(_1m(_1EM.a,_1EM.b,_1EM.c,_1EM.d,_1EM.e,_1EM.f,_1EM.g,_1EN,_1EM.i,_1EK));return {_:0,a:_1EP.a,b:_1EP.b,c:_1EP.c,d:_1EP.d,e:_1EP.e,f:_1EP.f,g:_1EP.g,h:_1EP.h,i:_1EP.i};}}else{return {_:0,a:_2P,b:_5L,c:_2P,d:_2P,e:_8R,f:_8S,g:_8L,h:_cj,i:_5K};}}else{var _1EQ=E(_1CC),_1ER=E(_1CF);if(_1EQ<=_1ER){var _1ES=new T(function(){var _1ET=E(_1E4),_1EU=B(_dk(_dl-_1ET|0,_ds,_1EQ,_1CE,_1E8,_1E1,_1E2,_1E3,_1ET,_1E5,_1E6,_1E7));return {_:0,a:_1EU.a,b:_1EU.b,c:_1EU.c,d:_1EU.d,e:_1EU.e,f:_1EU.f,g:_1EU.g,h:_1EU.h,i:_1EU.i};}),_1EV=function(_1EW,_1EX){var _1EY=E(_1EX);if(!_1EY._){return __Z;}else{var _1EZ=E(_1EW);if(_1EZ<=_1ER){var _1F0=new T(function(){var _1F1=E(_1EY.a),_1F2=_1F1.a,_1F3=_1F1.b,_1F4=_1F1.c,_1F5=_1F1.d,_1F6=_1F1.f,_1F7=_1F1.g,_1F8=_1F1.i,_1F9=E(_1F1.e),_1Fa=B(_dk(_dl-_1F9|0,_ds,_1EZ,_1EZ,_1F2,_1F3,_1F4,_1F5,_1F9,_1F6,_1F7,_1F8)),_1Fb=_1Fa.a,_1Fc=_1Fa.b,_1Fd=_1Fa.c,_1Fe=_1Fa.d,_1Ff=_1Fa.e,_1Fg=_1Fa.f,_1Fh=_1Fa.g,_1Fi=_1Fa.i,_1Fj=E(_1Fa.h);if(_1EZ>=_1Fj){return {_:0,a:_1Fb,b:_1Fc,c:_1Fd,d:_1Fe,e:_1Ff,f:_1Fg,g:_1Fh,h:_1Fj,i:_1Fi};}else{var _1Fk=E(_1CE);if(_1Fj>=_1Fk){return {_:0,a:_1Fb,b:_1Fc,c:_1Fd,d:_1Fe,e:_1Ff,f:_1Fg,g:_1Fh,h:_1Fj,i:_1Fi};}else{var _1Fl=B(_dk(_dl-_1F9|0,_ds,_1Fj,_1Fk,_1F2,_1F3,_1F4,_1F5,_1F9,_1F6,_1F7,_1F8));return {_:0,a:_1Fl.a,b:_1Fl.b,c:_1Fl.c,d:_1Fl.d,e:_1Fl.e,f:_1Fl.f,g:_1Fl.g,h:_1Fl.h,i:_1Fl.i};}}}),_1Fm=new T(function(){return B(_1EV(new T(function(){var _1Fn=E(E(_1F0).h);if(_1EZ>_1Fn){return E(_1EZ);}else{return E(_1Fn);}},1),_1EY.b));});return new T2(1,_1F0,_1Fm);}else{return __Z;}}},_1Fo=B(_1EV(new T(function(){var _1Fp=E(E(_1ES).h);if(_1EQ>_1Fp){return E(_1EQ);}else{return E(_1Fp);}},1),_1Ea)),_1Fq=E(_1ES),_1Fr=E(_1Fq.h);if(_1Fr<=(-2.1472688996352e9)){var _1Fs=B(_17(_2P,_5J,_2P,_2P,_8R,_8S,_8L,-2.1472688996352e9,_5K,_1Fo));return {_:0,a:_1Fs.a,b:_1Fs.b,c:_1Fs.c,d:_1Fs.d,e:_1Fs.e,f:_1Fs.f,g:_1Fs.g,h:_1Fs.h,i:_1Fs.i};}else{var _1Ft=B(_17(_1Fq.a,_1Fq.b,_1Fq.c,_1Fq.d,_1Fq.e,_1Fq.f,_1Fq.g,_1Fr,_1Fq.i,_1Fo));return {_:0,a:_1Ft.a,b:_1Ft.b,c:_1Ft.c,d:_1Ft.d,e:_1Ft.e,f:_1Ft.f,g:_1Ft.g,h:_1Ft.h,i:_1Ft.i};}}else{return {_:0,a:_2P,b:_5J,c:_2P,d:_2P,e:_8R,f:_8S,g:_8L,h:_ci,i:_5K};}}}}}),_1Fu=new T(function(){var _1Fv=function(_1Fw){var _1Fx=E(B(_dk(1,_ds,_dj,_di,_dB,new T(function(){return B(_co(_dq));}),_dr,_ds,_dt,_du,_dv,_dw)).h);return (!E(_dq))?(_1Fx>=2.145336163353e9)?5.0000000000000044e-2*E(_dv)+0.95*E(E(_1Cw).h):0:(_1Fx<=(-2.145336164352e9))?5.0000000000000044e-2*E(_dv)+0.95*E(E(_1Cw).h):0;};if(!E(_dq)){var _1Fy=E(E(_1Cw).h);if(_1Fy<=2.145336163353e9){return 5.0000000000000044e-2*E(_dv)+0.95*_1Fy;}else{return B(_1Fv(_));}}else{var _1Fz=E(E(_1Cw).h);if(_1Fz>=(-2.145336164352e9)){return 5.0000000000000044e-2*E(_dv)+0.95*_1Fz;}else{return B(_1Fv(_));}}});return {_:0,a:_dB,b:_dq,c:_dr,d:_ds,e:_dt,f:_du,g:_dv,h:_1Fu,i:new T1(1,_1Cw)};},_1FA=function(_1FB){var _1FC=function(_1FD){var _1FE=function(_1FF){var _1FG=function(_1FH){var _1FI=function(_1FJ){while(1){var _1FK=B((function(_1FL){var _1FM=E(_1FL);if(!_1FM._){return true;}else{var _1FN=_1FM.b,_1FO=E(_1FM.a);if(!_1FO._){return false;}else{var _1FP=_1FO.b,_1FQ=E(E(_1FO.a).b);if(!E(_dq)){if(E(_1FQ)==75){_1FJ=_1FN;return __continue;}else{var _1FR=function(_1FS){while(1){var _1FT=E(_1FS);if(!_1FT._){return false;}else{if(E(E(_1FT.a).b)==75){return true;}else{_1FS=_1FT.b;continue;}}}};if(!B(_1FR(_1FP))){return false;}else{_1FJ=_1FN;return __continue;}}}else{if(E(_1FQ)==107){_1FJ=_1FN;return __continue;}else{var _1FU=function(_1FV){while(1){var _1FW=E(_1FV);if(!_1FW._){return false;}else{if(E(E(_1FW.a).b)==107){return true;}else{_1FV=_1FW.b;continue;}}}};if(!B(_1FU(_1FP))){return false;}else{_1FJ=_1FN;return __continue;}}}}}})(_1FJ));if(_1FK!=__continue){return _1FK;}}};if(!B(_1FI(B(_ck(_8J,_VC))))){return {_:0,a:_dB,b:_dq,c:_dr,d:_ds,e:_dt,f:_du,g:_dv,h:new T(function(){if(!E(_dq)){return E(_dj);}else{return E(_di);}}),i:_5K};}else{return new F(function(){return _1Cu(_);});}},_1FX=function(_1FY){if(!B(_6g(B(_ck(_8J,_VC))))){return {_:0,a:_dB,b:_dq,c:_dr,d:_ds,e:_dt,f:_du,g:_dv,h:new T(function(){if(!E(_dq)){return E(_dj);}else{return E(_di);}}),i:_5K};}else{return new F(function(){return _1Cu(_);});}};if(!B(_q(_dm,3))){if(!B(_q(_ds,3))){return new F(function(){return _1FG(_);});}else{return new F(function(){return _1FX(_);});}}else{if(!B(_q(_ds,3))){return new F(function(){return _1FX(_);});}else{return new F(function(){return _1FG(_);});}}},_1FZ=function(_1G0){if(!B(_6y(B(_ck(_8J,_VC))))){return {_:0,a:_dB,b:_dq,c:_dr,d:_ds,e:_dt,f:_du,g:_dv,h:new T(function(){if(!E(_dq)){return E(_dj);}else{return E(_di);}}),i:_5K};}else{return new F(function(){return _1Cu(_);});}};if(!B(_q(_dm,2))){if(!B(_q(_ds,2))){return new F(function(){return _1FE(_);});}else{return new F(function(){return _1FZ(_);});}}else{if(!B(_q(_ds,2))){return new F(function(){return _1FZ(_);});}else{return new F(function(){return _1FE(_);});}}},_1G1=function(_1G2){if(!B(_6Q(B(_ck(_8J,_VC))))){return {_:0,a:_dB,b:_dq,c:_dr,d:_ds,e:_dt,f:_du,g:_dv,h:new T(function(){if(!E(_dq)){return E(_dj);}else{return E(_di);}}),i:_5K};}else{return new F(function(){return _1Cu(_);});}};if(!B(_q(_dm,1))){if(!B(_q(_ds,1))){return new F(function(){return _1FC(_);});}else{return new F(function(){return _1G1(_);});}}else{if(!B(_q(_ds,1))){return new F(function(){return _1G1(_);});}else{return new F(function(){return _1FC(_);});}}},_1G3=function(_1G4){if(!B(_78(B(_ck(_8J,_VC))))){return {_:0,a:_dB,b:_dq,c:_dr,d:_ds,e:_dt,f:_du,g:_dv,h:new T(function(){if(!E(_dq)){return E(_dj);}else{return E(_di);}}),i:_5K};}else{return new F(function(){return _1Cu(_);});}};if(!B(_q(_dm,0))){if(!B(_q(_ds,0))){return new F(function(){return _1FA(_);});}else{return new F(function(){return _1G3(_);});}}else{if(!B(_q(_ds,0))){return new F(function(){return _1G3(_);});}else{return new F(function(){return _1FA(_);});}}}}else{return {_:0,a:_dp,b:_dq,c:_dr,d:_ds,e:_dt,f:_du,g:_dv,h:_dv,i:_5K};}},_1G5=new T2(1,_5J,_2P),_1G6=new T2(1,_5J,_1G5),_1G7=new T2(1,_5J,_1G6),_1G8=new T2(1,_5J,_1G7),_1G9=function(_1Ga,_1Gb,_1Gc,_1Gd,_1Ge,_1Gf,_1Gg,_1Gh,_1Gi){var _1Gj=E(_1Ga);if(!_1Gj){return new F(function(){return _dk(0,_1G8,_dj,_di,_1Gb,_1Gc,_1Gd,_1Ge,_1Gf,_1Gg,_1Gh,_1Gi);});}else{var _1Gk=B(_1G9(_1Gj-1|0,_1Gb,_1Gc,_1Gd,_1Ge,_1Gf,_1Gg,_1Gh,_1Gi));return new F(function(){return _dk(_1Gj,_1G8,_dj,_di,_1Gk.a,_1Gk.b,_1Gk.c,_1Gk.d,_1Gk.e,_1Gk.f,_1Gk.g,_1Gk.i);});}},_1Gl=function(_1Gm,_1Gn){while(1){var _1Go=E(_1Gm);if(!_1Go._){return E(_1Gn);}else{var _1Gp=_1Gn+1|0;_1Gm=_1Go.b;_1Gn=_1Gp;continue;}}},_1Gq=new T(function(){return B(unCStr("ACK"));}),_1Gr=new T(function(){return B(unCStr("BEL"));}),_1Gs=new T(function(){return B(unCStr("BS"));}),_1Gt=new T(function(){return B(unCStr("SP"));}),_1Gu=new T2(1,_1Gt,_2P),_1Gv=new T(function(){return B(unCStr("US"));}),_1Gw=new T2(1,_1Gv,_1Gu),_1Gx=new T(function(){return B(unCStr("RS"));}),_1Gy=new T2(1,_1Gx,_1Gw),_1Gz=new T(function(){return B(unCStr("GS"));}),_1GA=new T2(1,_1Gz,_1Gy),_1GB=new T(function(){return B(unCStr("FS"));}),_1GC=new T2(1,_1GB,_1GA),_1GD=new T(function(){return B(unCStr("ESC"));}),_1GE=new T2(1,_1GD,_1GC),_1GF=new T(function(){return B(unCStr("SUB"));}),_1GG=new T2(1,_1GF,_1GE),_1GH=new T(function(){return B(unCStr("EM"));}),_1GI=new T2(1,_1GH,_1GG),_1GJ=new T(function(){return B(unCStr("CAN"));}),_1GK=new T2(1,_1GJ,_1GI),_1GL=new T(function(){return B(unCStr("ETB"));}),_1GM=new T2(1,_1GL,_1GK),_1GN=new T(function(){return B(unCStr("SYN"));}),_1GO=new T2(1,_1GN,_1GM),_1GP=new T(function(){return B(unCStr("NAK"));}),_1GQ=new T2(1,_1GP,_1GO),_1GR=new T(function(){return B(unCStr("DC4"));}),_1GS=new T2(1,_1GR,_1GQ),_1GT=new T(function(){return B(unCStr("DC3"));}),_1GU=new T2(1,_1GT,_1GS),_1GV=new T(function(){return B(unCStr("DC2"));}),_1GW=new T2(1,_1GV,_1GU),_1GX=new T(function(){return B(unCStr("DC1"));}),_1GY=new T2(1,_1GX,_1GW),_1GZ=new T(function(){return B(unCStr("DLE"));}),_1H0=new T2(1,_1GZ,_1GY),_1H1=new T(function(){return B(unCStr("SI"));}),_1H2=new T2(1,_1H1,_1H0),_1H3=new T(function(){return B(unCStr("SO"));}),_1H4=new T2(1,_1H3,_1H2),_1H5=new T(function(){return B(unCStr("CR"));}),_1H6=new T2(1,_1H5,_1H4),_1H7=new T(function(){return B(unCStr("FF"));}),_1H8=new T2(1,_1H7,_1H6),_1H9=new T(function(){return B(unCStr("VT"));}),_1Ha=new T2(1,_1H9,_1H8),_1Hb=new T(function(){return B(unCStr("LF"));}),_1Hc=new T2(1,_1Hb,_1Ha),_1Hd=new T(function(){return B(unCStr("HT"));}),_1He=new T2(1,_1Hd,_1Hc),_1Hf=new T2(1,_1Gs,_1He),_1Hg=new T2(1,_1Gr,_1Hf),_1Hh=new T2(1,_1Gq,_1Hg),_1Hi=new T(function(){return B(unCStr("ENQ"));}),_1Hj=new T2(1,_1Hi,_1Hh),_1Hk=new T(function(){return B(unCStr("EOT"));}),_1Hl=new T2(1,_1Hk,_1Hj),_1Hm=new T(function(){return B(unCStr("ETX"));}),_1Hn=new T2(1,_1Hm,_1Hl),_1Ho=new T(function(){return B(unCStr("STX"));}),_1Hp=new T2(1,_1Ho,_1Hn),_1Hq=new T(function(){return B(unCStr("SOH"));}),_1Hr=new T2(1,_1Hq,_1Hp),_1Hs=new T(function(){return B(unCStr("NUL"));}),_1Ht=new T2(1,_1Hs,_1Hr),_1Hu=92,_1Hv=new T(function(){return B(unCStr("\\DEL"));}),_1Hw=new T(function(){return B(unCStr("\\a"));}),_1Hx=new T(function(){return B(unCStr("\\\\"));}),_1Hy=new T(function(){return B(unCStr("\\SO"));}),_1Hz=new T(function(){return B(unCStr("\\r"));}),_1HA=new T(function(){return B(unCStr("\\f"));}),_1HB=new T(function(){return B(unCStr("\\v"));}),_1HC=new T(function(){return B(unCStr("\\n"));}),_1HD=new T(function(){return B(unCStr("\\t"));}),_1HE=new T(function(){return B(unCStr("\\b"));}),_1HF=function(_1HG,_1HH){if(_1HG<=127){var _1HI=E(_1HG);switch(_1HI){case 92:return new F(function(){return _a(_1Hx,_1HH);});break;case 127:return new F(function(){return _a(_1Hv,_1HH);});break;default:if(_1HI<32){var _1HJ=E(_1HI);switch(_1HJ){case 7:return new F(function(){return _a(_1Hw,_1HH);});break;case 8:return new F(function(){return _a(_1HE,_1HH);});break;case 9:return new F(function(){return _a(_1HD,_1HH);});break;case 10:return new F(function(){return _a(_1HC,_1HH);});break;case 11:return new F(function(){return _a(_1HB,_1HH);});break;case 12:return new F(function(){return _a(_1HA,_1HH);});break;case 13:return new F(function(){return _a(_1Hz,_1HH);});break;case 14:return new F(function(){return _a(_1Hy,new T(function(){var _1HK=E(_1HH);if(!_1HK._){return __Z;}else{if(E(_1HK.a)==72){return B(unAppCStr("\\&",_1HK));}else{return E(_1HK);}}},1));});break;default:return new F(function(){return _a(new T2(1,_1Hu,new T(function(){return B(_q(_1Ht,_1HJ));})),_1HH);});}}else{return new T2(1,_1HI,_1HH);}}}else{var _1HL=new T(function(){var _1HM=jsShowI(_1HG);return B(_a(fromJSStr(_1HM),new T(function(){var _1HN=E(_1HH);if(!_1HN._){return __Z;}else{var _1HO=E(_1HN.a);if(_1HO<48){return E(_1HN);}else{if(_1HO>57){return E(_1HN);}else{return B(unAppCStr("\\&",_1HN));}}}},1)));});return new T2(1,_1Hu,_1HL);}},_1HP=new T(function(){return B(unCStr("\'\\\'\'"));}),_1HQ=39,_1HR=function(_1HS,_1HT){var _1HU=E(_1HS);if(_1HU==39){return new F(function(){return _a(_1HP,_1HT);});}else{return new T2(1,_1HQ,new T(function(){return B(_1HF(_1HU,new T2(1,_1HQ,_1HT)));}));}},_1HV=function(_1HW){return new F(function(){return err(B(unAppCStr("Char.digitToInt: not a digit ",new T(function(){return B(_1HR(_1HW,_2P));}))));});},_1HX=function(_1HY){var _1HZ=_1HY-48|0;if(_1HZ>>>0>9){var _1I0=_1HY-97|0;if(_1I0>>>0>5){var _1I1=_1HY-65|0;if(_1I1>>>0>5){return new F(function(){return _1HV(_1HY);});}else{return _1I1+10|0;}}else{return _1I0+10|0;}}else{return E(_1HZ);}},_1I2=function(_1I3){return new F(function(){return err(B(unAppCStr("Char.intToDigit: not a digit ",new T(function(){if(_1I3>=0){var _1I4=jsShowI(_1I3);return fromJSStr(_1I4);}else{var _1I5=jsShowI(_1I3);return fromJSStr(_1I5);}}))));});},_1I6=function(_1I7){var _1I8=function(_1I9){if(_1I7<10){return new F(function(){return _1I2(_1I7);});}else{if(_1I7>15){return new F(function(){return _1I2(_1I7);});}else{return (97+_1I7|0)-10|0;}}};if(_1I7<0){return new F(function(){return _1I8(_);});}else{if(_1I7>9){return new F(function(){return _1I8(_);});}else{return 48+_1I7|0;}}},_1Ia=function(_1Ib,_1Ic,_1Id,_1Ie,_1If,_1Ig,_1Ih,_1Ii,_1Ij,_1Ik,_1Il,_1Im,_1In){while(1){var _1Io=B((function(_1Ip,_1Iq,_1Ir,_1Is,_1It,_1Iu,_1Iv,_1Iw,_1Ix,_1Iy,_1Iz,_1IA,_1IB){var _1IC=E(_1Ip),_1ID=E(_1IC);switch(_1ID){case 32:return {_:0,a:_1It,b:_1Iu,c:_1Iv,d:_1Iw,e:_1Ix,f:_1Iy,g:_1Iz,h:_1IA,i:_1IB};case 47:return new F(function(){return _1IE(_1Iq,1,_1Is-1|0,_1It,_1Iu,_1Iv,_1Iw,_1Ix,_1Iy,_1Iz,_1IA,_1IB);});break;default:if((_1ID-48|0)>>>0>9){return new F(function(){return _1IE(_1Iq,_1Ir+1|0,_1Is,new T2(1,new T2(0,new T2(0,_1Ir,_1Is),_1IC),_1It),_1Iu,_1Iv,_1Iw,_1Ix,_1Iy,_1Iz,_1IA,_1IB);});}else{var _1IF=E(_1ID);if(_1IF==49){return new F(function(){return _1IE(_1Iq,_1Ir+1|0,_1Is,_1It,_1Iu,_1Iv,_1Iw,_1Ix,_1Iy,_1Iz,_1IA,_1IB);});}else{var _1IG=_1Iq,_1IH=_1Ir+1|0,_1II=_1Is,_1IJ=_1It,_1IK=_1Iu,_1IL=_1Iv,_1IM=_1Iw,_1IN=_1Ix,_1IO=_1Iy,_1IP=_1Iz,_1IQ=_1IA,_1IR=_1IB;_1Ib=new T(function(){return B(_1I6(B(_1HX(_1IF))-1|0));});_1Ic=_1IG;_1Id=_1IH;_1Ie=_1II;_1If=_1IJ;_1Ig=_1IK;_1Ih=_1IL;_1Ii=_1IM;_1Ij=_1IN;_1Ik=_1IO;_1Il=_1IP;_1Im=_1IQ;_1In=_1IR;return __continue;}}}})(_1Ib,_1Ic,_1Id,_1Ie,_1If,_1Ig,_1Ih,_1Ii,_1Ij,_1Ik,_1Il,_1Im,_1In));if(_1Io!=__continue){return _1Io;}}},_1IE=function(_1IS,_1IT,_1IU,_1IV,_1IW,_1IX,_1IY,_1IZ,_1J0,_1J1,_1J2,_1J3){while(1){var _1J4=B((function(_1J5,_1J6,_1J7,_1J8,_1J9,_1Ja,_1Jb,_1Jc,_1Jd,_1Je,_1Jf,_1Jg){var _1Jh=E(_1J5);if(!_1Jh._){return E(_5Q);}else{var _1Ji=_1Jh.b,_1Jj=E(_1Jh.a),_1Jk=E(_1Jj);switch(_1Jk){case 32:return {_:0,a:_1J8,b:_1J9,c:_1Ja,d:_1Jb,e:_1Jc,f:_1Jd,g:_1Je,h:_1Jf,i:_1Jg};case 47:var _1Jl=_1J7-1|0,_1Jm=_1J8,_1Jn=_1J9,_1Jo=_1Ja,_1Jp=_1Jb,_1Jq=_1Jc,_1Jr=_1Jd,_1Js=_1Je,_1Jt=_1Jf,_1Ju=_1Jg;_1IS=_1Ji;_1IT=1;_1IU=_1Jl;_1IV=_1Jm;_1IW=_1Jn;_1IX=_1Jo;_1IY=_1Jp;_1IZ=_1Jq;_1J0=_1Jr;_1J1=_1Js;_1J2=_1Jt;_1J3=_1Ju;return __continue;default:if((_1Jk-48|0)>>>0>9){var _1Jv=_1J6+1|0,_1Jl=_1J7,_1Jm=new T2(1,new T2(0,new T2(0,_1J6,_1J7),_1Jj),_1J8),_1Jn=_1J9,_1Jo=_1Ja,_1Jp=_1Jb,_1Jq=_1Jc,_1Jr=_1Jd,_1Js=_1Je,_1Jt=_1Jf,_1Ju=_1Jg;_1IS=_1Ji;_1IT=_1Jv;_1IU=_1Jl;_1IV=_1Jm;_1IW=_1Jn;_1IX=_1Jo;_1IY=_1Jp;_1IZ=_1Jq;_1J0=_1Jr;_1J1=_1Js;_1J2=_1Jt;_1J3=_1Ju;return __continue;}else{var _1Jw=E(_1Jk);if(_1Jw==49){var _1Jv=_1J6+1|0,_1Jl=_1J7,_1Jm=_1J8,_1Jn=_1J9,_1Jo=_1Ja,_1Jp=_1Jb,_1Jq=_1Jc,_1Jr=_1Jd,_1Js=_1Je,_1Jt=_1Jf,_1Ju=_1Jg;_1IS=_1Ji;_1IT=_1Jv;_1IU=_1Jl;_1IV=_1Jm;_1IW=_1Jn;_1IX=_1Jo;_1IY=_1Jp;_1IZ=_1Jq;_1J0=_1Jr;_1J1=_1Js;_1J2=_1Jt;_1J3=_1Ju;return __continue;}else{return new F(function(){return _1Ia(new T(function(){return B(_1I6(B(_1HX(_1Jw))-1|0));}),_1Ji,_1J6+1|0,_1J7,_1J8,_1J9,_1Ja,_1Jb,_1Jc,_1Jd,_1Je,_1Jf,_1Jg);});}}}}})(_1IS,_1IT,_1IU,_1IV,_1IW,_1IX,_1IY,_1IZ,_1J0,_1J1,_1J2,_1J3));if(_1J4!=__continue){return _1J4;}}},_1Jx=new T(function(){return B(_49("Main.hs:(173,9)-(179,120)|function castler"));}),_1Jy=function(_1Jz,_1JA,_1JB,_1JC,_1JD,_1JE,_1JF,_1JG,_1JH,_1JI){while(1){var _1JJ=B((function(_1JK,_1JL,_1JM,_1JN,_1JO,_1JP,_1JQ,_1JR,_1JS,_1JT){var _1JU=E(_1JK);if(!_1JU._){return E(_5Q);}else{var _1JV=_1JU.b;switch(E(_1JU.a)){case 32:return {_:0,a:_1JL,b:_1JM,c:_1JN,d:_1JO,e:_1JP,f:_1JQ,g:_1JR,h:_1JS,i:_1JT};case 45:return {_:0,a:_1JL,b:_1JM,c:_1JN,d:_1JO,e:_1JP,f:_1JQ,g:_1JR,h:_1JS,i:_1JT};case 75:var _1JW=_1JL,_1JX=_1JM,_1JY=_1JO,_1JZ=_1JP,_1K0=_1JQ,_1K1=_1JR,_1K2=_1JS,_1K3=_1JT;_1Jz=_1JV;_1JA=_1JW;_1JB=_1JX;_1JC=new T(function(){return B(_5B(0,_5J,_1JN));});_1JD=_1JY;_1JE=_1JZ;_1JF=_1K0;_1JG=_1K1;_1JH=_1K2;_1JI=_1K3;return __continue;case 81:var _1JW=_1JL,_1JX=_1JM,_1JY=_1JO,_1JZ=_1JP,_1K0=_1JQ,_1K1=_1JR,_1K2=_1JS,_1K3=_1JT;_1Jz=_1JV;_1JA=_1JW;_1JB=_1JX;_1JC=new T(function(){return B(_5B(1,_5J,_1JN));});_1JD=_1JY;_1JE=_1JZ;_1JF=_1K0;_1JG=_1K1;_1JH=_1K2;_1JI=_1K3;return __continue;case 107:var _1JW=_1JL,_1JX=_1JM,_1JY=_1JO,_1JZ=_1JP,_1K0=_1JQ,_1K1=_1JR,_1K2=_1JS,_1K3=_1JT;_1Jz=_1JV;_1JA=_1JW;_1JB=_1JX;_1JC=new T(function(){return B(_5B(2,_5J,_1JN));});_1JD=_1JY;_1JE=_1JZ;_1JF=_1K0;_1JG=_1K1;_1JH=_1K2;_1JI=_1K3;return __continue;case 113:var _1JW=_1JL,_1JX=_1JM,_1JY=_1JO,_1JZ=_1JP,_1K0=_1JQ,_1K1=_1JR,_1K2=_1JS,_1K3=_1JT;_1Jz=_1JV;_1JA=_1JW;_1JB=_1JX;_1JC=new T(function(){return B(_5B(3,_5J,_1JN));});_1JD=_1JY;_1JE=_1JZ;_1JF=_1K0;_1JG=_1K1;_1JH=_1K2;_1JI=_1K3;return __continue;default:return E(_1Jx);}}})(_1Jz,_1JA,_1JB,_1JC,_1JD,_1JE,_1JF,_1JG,_1JH,_1JI));if(_1JJ!=__continue){return _1JJ;}}},_1K4=function(_1K5){while(1){var _1K6=E(_1K5);if(!_1K6._){return E(_5Q);}else{var _1K7=_1K6.b;if(E(_1K6.a)==32){return E(_1K7);}else{_1K5=_1K7;continue;}}}},_1K8=new T(function(){return B(_49("Main.hs:(162,49)-(170,101)|case"));}),_1K9=new T2(1,_5L,_2P),_1Ka=new T2(1,_5L,_1K9),_1Kb=new T2(1,_5L,_1Ka),_1Kc=new T2(1,_5L,_1Kb),_1Kd=function(_1Ke){var _1Kf=B(_1K4(_1Ke)),_1Kg=B(_1K4(_1Kf)),_1Kh=B(_1K4(_1Kg));if(!_1Kh._){return E(_5Q);}else{var _1Ki=_1Kh.b,_1Kj=B(_1IE(_1Ke,1,8,_2P,_5L,_1Kc,_1G8,_8R,_8S,_8L,_8L,_5K)),_1Kk=B(_1Jy(_1Kg,_1Kj.a,new T(function(){var _1Kl=E(_1Kf);if(!_1Kl._){return E(_5Q);}else{if(E(_1Kl.a)==119){return true;}else{return false;}}}),_1Kj.c,_1Kj.d,_1Kj.e,_1Kj.f,_1Kj.g,_1Kj.h,_1Kj.i)),_1Km=_1Kk.a,_1Kn=_1Kk.b,_1Ko=_1Kk.c,_1Kp=_1Kk.d,_1Kq=_1Kk.e,_1Kr=_1Kk.h,_1Ks=_1Kk.i;switch(E(_1Kh.a)){case 45:return new F(function(){return _8e(_1Km,_1Kn,_1Ko,_1Kp,_1Kq,_1Kk.f,_1Kr,_1Ks);});break;case 97:return new F(function(){return _8e(_1Km,_1Kn,_1Ko,_1Kp,_1Kq,new T2(0,_8U,new T(function(){var _1Kt=E(_1Ki);if(!_1Kt._){return E(_5Q);}else{return B(_1HX(E(_1Kt.a)));}})),_1Kr,_1Ks);});break;case 98:return new F(function(){return _8e(_1Km,_1Kn,_1Ko,_1Kp,_1Kq,new T2(0,_8M,new T(function(){var _1Ku=E(_1Ki);if(!_1Ku._){return E(_5Q);}else{return B(_1HX(E(_1Ku.a)));}})),_1Kr,_1Ks);});break;case 99:return new F(function(){return _8e(_1Km,_1Kn,_1Ko,_1Kp,_1Kq,new T2(0,_8N,new T(function(){var _1Kv=E(_1Ki);if(!_1Kv._){return E(_5Q);}else{return B(_1HX(E(_1Kv.a)));}})),_1Kr,_1Ks);});break;case 100:return new F(function(){return _8e(_1Km,_1Kn,_1Ko,_1Kp,_1Kq,new T2(0,_8O,new T(function(){var _1Kw=E(_1Ki);if(!_1Kw._){return E(_5Q);}else{return B(_1HX(E(_1Kw.a)));}})),_1Kr,_1Ks);});break;case 101:return new F(function(){return _8e(_1Km,_1Kn,_1Ko,_1Kp,_1Kq,new T2(0,_8P,new T(function(){var _1Kx=E(_1Ki);if(!_1Kx._){return E(_5Q);}else{return B(_1HX(E(_1Kx.a)));}})),_1Kr,_1Ks);});break;case 102:return new F(function(){return _8e(_1Km,_1Kn,_1Ko,_1Kp,_1Kq,new T2(0,_8Q,new T(function(){var _1Ky=E(_1Ki);if(!_1Ky._){return E(_5Q);}else{return B(_1HX(E(_1Ky.a)));}})),_1Kr,_1Ks);});break;case 103:return new F(function(){return _8e(_1Km,_1Kn,_1Ko,_1Kp,_1Kq,new T2(0,_8Y,new T(function(){var _1Kz=E(_1Ki);if(!_1Kz._){return E(_5Q);}else{return B(_1HX(E(_1Kz.a)));}})),_1Kr,_1Ks);});break;case 104:return new F(function(){return _8e(_1Km,_1Kn,_1Ko,_1Kp,_1Kq,new T2(0,_96,new T(function(){var _1KA=E(_1Ki);if(!_1KA._){return E(_5Q);}else{return B(_1HX(E(_1KA.a)));}})),_1Kr,_1Ks);});break;default:return E(_1K8);}}},_1KB=new T(function(){return B(unCStr("(Array.!): undefined array element"));}),_1KC=new T(function(){return B(err(_1KB));}),_1KD=new T(function(){return B(unCStr("Error in array index"));}),_1KE=new T(function(){return B(err(_1KD));}),_1KF=new T2(0,_8U,_8U),_1KG=new T2(0,_96,_96),_1KH=95,_1KI=function(_1KJ,_1KK){if(_1KJ<=_1KK){var _1KL=function(_1KM){return new T2(1,_1KM,new T(function(){if(_1KM!=_1KK){return B(_1KL(_1KM+1|0));}else{return __Z;}}));};return new F(function(){return _1KL(_1KJ);});}else{return __Z;}},_1KN=new T(function(){return B(_1KI(1,8));}),_1KO=function(_1KP){var _1KQ=B(A1(_1KP,_));return E(_1KQ);},_1KR=function(_1KS){var _1KT=function(_){var _1KU=newArr(64,_1KC),_1KV=_1KU,_1KW=function(_1KX,_){while(1){var _1KY=E(_1KX);if(!_1KY._){return new T4(0,E(_1KF),E(_1KG),64,_1KV);}else{var _1KZ=E(_1KY.a),_1L0=E(_1KZ.a),_1L1=E(_1L0.a);if(1>_1L1){return E(_1KE);}else{if(_1L1>8){return E(_1KE);}else{var _1L2=E(_1L0.b);if(1>_1L2){return E(_1KE);}else{if(_1L2>8){return E(_1KE);}else{var _=_1KV[(imul(_1L1-1|0,8)|0)+(_1L2-1|0)|0]=_1KZ.b;_1KX=_1KY.b;continue;}}}}}}},_1L3=function(_1L4,_){while(1){var _1L5=B((function(_1L6,_){var _1L7=E(_1KN);if(!_1L7._){var _1L8=E(_1L6);if(_1L8==8){return new F(function(){return _1KW(_1KS,_);});}else{_1L4=_1L8+1|0;return __continue;}}else{if(1>_1L6){return E(_1KE);}else{if(_1L6>8){return E(_1KE);}else{var _1L9=E(_1L7.a);if(1>_1L9){return E(_1KE);}else{if(_1L9>8){return E(_1KE);}else{var _=_1KV[(imul(_1L6-1|0,8)|0)+(_1L9-1|0)|0]=_1KH,_1La=function(_1Lb,_){while(1){var _1Lc=E(_1Lb);if(!_1Lc._){var _1Ld=E(_1L6);if(_1Ld==8){return new F(function(){return _1KW(_1KS,_);});}else{return new F(function(){return _1L3(_1Ld+1|0,_);});}}else{var _1Le=E(_1Lc.a);if(1>_1Le){return E(_1KE);}else{if(_1Le>8){return E(_1KE);}else{var _=_1KV[(imul(_1L6-1|0,8)|0)+(_1Le-1|0)|0]=_1KH;_1Lb=_1Lc.b;continue;}}}}};return new F(function(){return _1La(_1L7.b,_);});}}}}}})(_1L4,_));if(_1L5!=__continue){return _1L5;}}};return new F(function(){return _1L3(1,_);});};return new F(function(){return _1KO(_1KT);});},_1Lf=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_1Lg=new T(function(){return B(err(_1Lf));}),_1Lh=new T(function(){return B(unCStr("last"));}),_1Li=new T(function(){return B(_5N(_1Lh));}),_1Lj=new T(function(){return B(_1KI(0,63));}),_1Lk=new T(function(){return B(_49("Main.hs:(142,49)-(150,278)|case"));}),_1Ll=new T(function(){return B(_49("Main.hs:(142,74)-(145,106)|case"));}),_1Lm=function(_1Ln,_1Lo){var _1Lp=_1Ln%_1Lo;if(_1Ln<=0){if(_1Ln>=0){return E(_1Lp);}else{if(_1Lo<=0){return E(_1Lp);}else{var _1Lq=E(_1Lp);return (_1Lq==0)?0:_1Lq+_1Lo|0;}}}else{if(_1Lo>=0){if(_1Ln>=0){return E(_1Lp);}else{if(_1Lo<=0){return E(_1Lp);}else{var _1Lr=E(_1Lp);return (_1Lr==0)?0:_1Lr+_1Lo|0;}}}else{var _1Ls=E(_1Lp);return (_1Ls==0)?0:_1Ls+_1Lo|0;}}},_1Lt=function(_1Lu,_1Lv){var _1Lw=new T(function(){var _1Lx=B(_1Kd(_1Lu)),_1Ly=B(_1G9(E(_1Lv),_1Lx.a,_1Lx.b,_1Lx.c,_1Lx.d,_1Lx.e,_1Lx.f,_1Lx.g,_1Lx.i));return {_:0,a:_1Ly.a,b:_1Ly.b,c:_1Ly.c,d:_1Ly.d,e:_1Ly.e,f:_1Ly.f,g:_1Ly.g,h:_1Ly.h,i:_1Ly.i};}),_1Lz=new T(function(){var _1LA=E(E(_1Lw).i);if(!_1LA._){return E(_1Lg);}else{var _1LB=B(_1KR(E(_1LA.a).a)),_1LC=_1LB.d,_1LD=E(_1LB.a),_1LE=E(_1LB.b),_1LF=E(_1LD.a),_1LG=E(_1LE.a);if(_1LF<=_1LG){var _1LH=E(_1LD.b),_1LI=E(_1LE.b),_1LJ=new T(function(){if(_1LF!=_1LG){var _1LK=function(_1LL){var _1LM=new T(function(){if(_1LL!=_1LG){return B(_1LK(_1LL+1|0));}else{return __Z;}});if(_1LH<=_1LI){var _1LN=new T(function(){return _1LF<=_1LL;}),_1LO=new T(function(){return _1LL<=_1LG;}),_1LP=function(_1LQ){return new T2(1,new T2(0,new T2(0,_1LL,_1LQ),new T(function(){if(!E(_1LN)){return E(_1KE);}else{if(!E(_1LO)){return E(_1KE);}else{if(_1LH>_1LQ){return E(_1KE);}else{if(_1LQ>_1LI){return E(_1KE);}else{return E(_1LC[(imul(_1LL-_1LF|0,(_1LI-_1LH|0)+1|0)|0)+(_1LQ-_1LH|0)|0]);}}}}})),new T(function(){if(_1LQ!=_1LI){return B(_1LP(_1LQ+1|0));}else{return E(_1LM);}}));};return new F(function(){return _1LP(_1LH);});}else{return E(_1LM);}};return B(_1LK(_1LF+1|0));}else{return __Z;}});if(_1LH<=_1LI){var _1LR=new T(function(){return _1LF<=_1LG;}),_1LS=function(_1LT){return new T2(1,new T2(0,new T2(0,_1LF,_1LT),new T(function(){if(!E(_1LR)){return E(_1KE);}else{if(_1LH>_1LT){return E(_1KE);}else{if(_1LT>_1LI){return E(_1KE);}else{return E(_1LC[_1LT-_1LH|0]);}}}})),new T(function(){if(_1LT!=_1LI){return B(_1LS(_1LT+1|0));}else{return E(_1LJ);}}));};return B(_1LS(_1LH));}else{return E(_1LJ);}}else{return __Z;}}}),_1LU=new T(function(){var _1LV=B(_1KR(E(_1Lw).a)),_1LW=_1LV.d,_1LX=E(_1LV.a),_1LY=E(_1LV.b),_1LZ=E(_1LX.a),_1M0=E(_1LY.a);if(_1LZ<=_1M0){var _1M1=E(_1LX.b),_1M2=E(_1LY.b),_1M3=new T(function(){if(_1LZ!=_1M0){var _1M4=function(_1M5){var _1M6=new T(function(){if(_1M5!=_1M0){return B(_1M4(_1M5+1|0));}else{return __Z;}});if(_1M1<=_1M2){var _1M7=new T(function(){return _1LZ<=_1M5;}),_1M8=new T(function(){return _1M5<=_1M0;}),_1M9=function(_1Ma){return new T2(1,new T2(0,new T2(0,_1M5,_1Ma),new T(function(){if(!E(_1M7)){return E(_1KE);}else{if(!E(_1M8)){return E(_1KE);}else{if(_1M1>_1Ma){return E(_1KE);}else{if(_1Ma>_1M2){return E(_1KE);}else{return E(_1LW[(imul(_1M5-_1LZ|0,(_1M2-_1M1|0)+1|0)|0)+(_1Ma-_1M1|0)|0]);}}}}})),new T(function(){if(_1Ma!=_1M2){return B(_1M9(_1Ma+1|0));}else{return E(_1M6);}}));};return new F(function(){return _1M9(_1M1);});}else{return E(_1M6);}};return B(_1M4(_1LZ+1|0));}else{return __Z;}});if(_1M1<=_1M2){var _1Mb=new T(function(){return _1LZ<=_1M0;}),_1Mc=function(_1Md){return new T2(1,new T2(0,new T2(0,_1LZ,_1Md),new T(function(){if(!E(_1Mb)){return E(_1KE);}else{if(_1M1>_1Md){return E(_1KE);}else{if(_1Md>_1M2){return E(_1KE);}else{return E(_1LW[_1Md-_1M1|0]);}}}})),new T(function(){if(_1Md!=_1M2){return B(_1Mc(_1Md+1|0));}else{return E(_1M3);}}));};return B(_1Mc(_1M1));}else{return E(_1M3);}}else{return __Z;}}),_1Me=B(_5R(function(_1Mf){var _1Mg=E(_1Mf),_1Mh=B(_q(_1LU,_1Mg)),_1Mi=B(_q(_1Lz,_1Mg)),_1Mj=E(_1Mh.a),_1Mk=E(_1Mi.a);return (E(_1Mj.a)!=E(_1Mk.a))?true:(E(_1Mj.b)!=E(_1Mk.b))?true:(E(_1Mh.b)!=E(_1Mi.b))?true:false;},_1Lj));switch(B(_1Gl(_1Me,0))){case 2:var _1Ml=E(_1Me);return (_1Ml._==0)?E(_5Q):(E(B(_q(_1Lz,E(_1Ml.a))).b)==95)?new T4(0,new T(function(){return quot(B(_q(_1Ml,0)),8)+1|0;}),new T(function(){return B(_1Lm(B(_q(_1Ml,0)),8))+1|0;}),new T(function(){return quot(B(_q(_1Ml,1)),8)+1|0;}),new T(function(){return B(_1Lm(B(_q(_1Ml,1)),8))+1|0;})):new T4(0,new T(function(){return quot(B(_q(_1Ml,1)),8)+1|0;}),new T(function(){return B(_1Lm(B(_q(_1Ml,1)),8))+1|0;}),new T(function(){return quot(B(_q(_1Ml,0)),8)+1|0;}),new T(function(){return B(_1Lm(B(_q(_1Ml,0)),8))+1|0;}));case 3:var _1Mm=E(_1Me);if(!_1Mm._){return E(_5Q);}else{var _1Mn=E(_1Mm.a),_1Mo=B(_1Lm(_1Mn,8));if(_1Mo>3){return (B(_1Lm(B(_6(_1Mn,_1Mm.b,_1Li)),8))==5)?new T4(0,quot(_1Mn,8)+1|0,_1Mo+1|0,quot(_1Mn,8)+2|0,_1Mo+2|0):new T4(0,quot(_1Mn,8)+2|0,_1Mo+1|0,quot(_1Mn,8)+1|0,_1Mo+2|0);}else{var _1Mp=E(_1Mo);return (_1Mp==3)?new T4(0,quot(_1Mn,8)+1|0,4,quot(_1Mn,8)+2|0,3):new T4(0,quot(_1Mn,8)+2|0,_1Mp+2|0,quot(_1Mn,8)+1|0,_1Mp+1|0);}}break;case 4:var _1Mq=E(_1Me);if(!_1Mq._){return E(_5Q);}else{switch(E(_1Mq.a)){case 0:return new T4(0,_8P,_8U,_8N,_8U);case 7:return new T4(0,_8P,_96,_8N,_96);case 32:return new T4(0,_8P,_8U,_8Y,_8U);case 39:return new T4(0,_8P,_96,_8Y,_96);default:return E(_1Ll);}}break;default:return E(_1Lk);}},_1Mr=new T(function(){return eval("(function(s,f){Haste[s] = f;})");}),_1Ms=function(_1Mt){return E(_1Mt);},_1Mu=function(_){var _1Mv=function(_1Mw){var _1Mx=new T(function(){var _1My=String(E(_1Mw));return fromJSStr(_1My);}),_1Mz=function(_1MA){var _1MB=B(_1Lt(_1Mx,new T(function(){var _1MC=Number(E(_1MA));return jsTrunc(_1MC);},1)));return new F(function(){return __lst2arr(B(_ck(_1Ms,new T2(1,_1MB.a,new T2(1,_1MB.b,new T2(1,_1MB.c,new T2(1,_1MB.d,_2P)))))));});};return E(_1Mz);},_1MD=__createJSFunc(2,E(_1Mv)),_1ME=__app2(E(_1Mr),"mover",_1MD);return new F(function(){return _1(_);});},_1MF=function(_){return new F(function(){return _1Mu(_);});};
var hasteMain = function() {B(A(_1MF, [0]));};window.onload = hasteMain;