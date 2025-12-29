'use strict';

var React$1 = require('react');
var ReactDOM = require('react-dom');

/******************************************************************************
Copyright (c) Microsoft Corporation.

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH
REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY
AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT,
INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM
LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR
OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
PERFORMANCE OF THIS SOFTWARE.
***************************************************************************** */
/* global Reflect, Promise, SuppressedError, Symbol */


var __assign$1 = function() {
    __assign$1 = Object.assign || function __assign(t) {
        for (var s, i = 1, n = arguments.length; i < n; i++) {
            s = arguments[i];
            for (var p in s) if (Object.prototype.hasOwnProperty.call(s, p)) t[p] = s[p];
        }
        return t;
    };
    return __assign$1.apply(this, arguments);
};

function __rest$1(s, e) {
    var t = {};
    for (var p in s) if (Object.prototype.hasOwnProperty.call(s, p) && e.indexOf(p) < 0)
        t[p] = s[p];
    if (s != null && typeof Object.getOwnPropertySymbols === "function")
        for (var i = 0, p = Object.getOwnPropertySymbols(s); i < p.length; i++) {
            if (e.indexOf(p[i]) < 0 && Object.prototype.propertyIsEnumerable.call(s, p[i]))
                t[p[i]] = s[p[i]];
        }
    return t;
}

function __spreadArray(to, from, pack) {
    if (pack || arguments.length === 2) for (var i = 0, l = from.length, ar; i < l; i++) {
        if (ar || !(i in from)) {
            if (!ar) ar = Array.prototype.slice.call(from, 0, i);
            ar[i] = from[i];
        }
    }
    return to.concat(ar || Array.prototype.slice.call(from));
}

typeof SuppressedError === "function" ? SuppressedError : function (error, suppressed, message) {
    var e = new Error(message);
    return e.name = "SuppressedError", e.error = error, e.suppressed = suppressed, e;
};

var commonjsGlobal = typeof globalThis !== 'undefined' ? globalThis : typeof window !== 'undefined' ? window : typeof global !== 'undefined' ? global : typeof self !== 'undefined' ? self : {};

function getDefaultExportFromCjs$1 (x) {
	return x && x.__esModule && Object.prototype.hasOwnProperty.call(x, 'default') ? x['default'] : x;
}

var propTypes$1 = {exports: {}};

var reactIs$1 = {exports: {}};

var reactIs_production_min$1 = {};

/** @license React v16.13.1
 * react-is.production.min.js
 *
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

var hasRequiredReactIs_production_min$1;

function requireReactIs_production_min$1 () {
	if (hasRequiredReactIs_production_min$1) return reactIs_production_min$1;
	hasRequiredReactIs_production_min$1 = 1;
var b="function"===typeof Symbol&&Symbol.for,c=b?Symbol.for("react.element"):60103,d=b?Symbol.for("react.portal"):60106,e=b?Symbol.for("react.fragment"):60107,f=b?Symbol.for("react.strict_mode"):60108,g=b?Symbol.for("react.profiler"):60114,h=b?Symbol.for("react.provider"):60109,k=b?Symbol.for("react.context"):60110,l=b?Symbol.for("react.async_mode"):60111,m=b?Symbol.for("react.concurrent_mode"):60111,n=b?Symbol.for("react.forward_ref"):60112,p=b?Symbol.for("react.suspense"):60113,q=b?
	Symbol.for("react.suspense_list"):60120,r=b?Symbol.for("react.memo"):60115,t=b?Symbol.for("react.lazy"):60116,v=b?Symbol.for("react.block"):60121,w=b?Symbol.for("react.fundamental"):60117,x=b?Symbol.for("react.responder"):60118,y=b?Symbol.for("react.scope"):60119;
	function z(a){if("object"===typeof a&&null!==a){var u=a.$$typeof;switch(u){case c:switch(a=a.type,a){case l:case m:case e:case g:case f:case p:return a;default:switch(a=a&&a.$$typeof,a){case k:case n:case t:case r:case h:return a;default:return u}}case d:return u}}}function A(a){return z(a)===m}reactIs_production_min$1.AsyncMode=l;reactIs_production_min$1.ConcurrentMode=m;reactIs_production_min$1.ContextConsumer=k;reactIs_production_min$1.ContextProvider=h;reactIs_production_min$1.Element=c;reactIs_production_min$1.ForwardRef=n;reactIs_production_min$1.Fragment=e;reactIs_production_min$1.Lazy=t;reactIs_production_min$1.Memo=r;reactIs_production_min$1.Portal=d;
	reactIs_production_min$1.Profiler=g;reactIs_production_min$1.StrictMode=f;reactIs_production_min$1.Suspense=p;reactIs_production_min$1.isAsyncMode=function(a){return A(a)||z(a)===l};reactIs_production_min$1.isConcurrentMode=A;reactIs_production_min$1.isContextConsumer=function(a){return z(a)===k};reactIs_production_min$1.isContextProvider=function(a){return z(a)===h};reactIs_production_min$1.isElement=function(a){return "object"===typeof a&&null!==a&&a.$$typeof===c};reactIs_production_min$1.isForwardRef=function(a){return z(a)===n};reactIs_production_min$1.isFragment=function(a){return z(a)===e};reactIs_production_min$1.isLazy=function(a){return z(a)===t};
	reactIs_production_min$1.isMemo=function(a){return z(a)===r};reactIs_production_min$1.isPortal=function(a){return z(a)===d};reactIs_production_min$1.isProfiler=function(a){return z(a)===g};reactIs_production_min$1.isStrictMode=function(a){return z(a)===f};reactIs_production_min$1.isSuspense=function(a){return z(a)===p};
	reactIs_production_min$1.isValidElementType=function(a){return "string"===typeof a||"function"===typeof a||a===e||a===m||a===g||a===f||a===p||a===q||"object"===typeof a&&null!==a&&(a.$$typeof===t||a.$$typeof===r||a.$$typeof===h||a.$$typeof===k||a.$$typeof===n||a.$$typeof===w||a.$$typeof===x||a.$$typeof===y||a.$$typeof===v)};reactIs_production_min$1.typeOf=z;
	return reactIs_production_min$1;
}

var reactIs_development$1 = {};

/** @license React v16.13.1
 * react-is.development.js
 *
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

var hasRequiredReactIs_development$1;

function requireReactIs_development$1 () {
	if (hasRequiredReactIs_development$1) return reactIs_development$1;
	hasRequiredReactIs_development$1 = 1;



	if (process.env.NODE_ENV !== "production") {
	  (function() {

	// The Symbol used to tag the ReactElement-like types. If there is no native Symbol
	// nor polyfill, then a plain number is used for performance.
	var hasSymbol = typeof Symbol === 'function' && Symbol.for;
	var REACT_ELEMENT_TYPE = hasSymbol ? Symbol.for('react.element') : 0xeac7;
	var REACT_PORTAL_TYPE = hasSymbol ? Symbol.for('react.portal') : 0xeaca;
	var REACT_FRAGMENT_TYPE = hasSymbol ? Symbol.for('react.fragment') : 0xeacb;
	var REACT_STRICT_MODE_TYPE = hasSymbol ? Symbol.for('react.strict_mode') : 0xeacc;
	var REACT_PROFILER_TYPE = hasSymbol ? Symbol.for('react.profiler') : 0xead2;
	var REACT_PROVIDER_TYPE = hasSymbol ? Symbol.for('react.provider') : 0xeacd;
	var REACT_CONTEXT_TYPE = hasSymbol ? Symbol.for('react.context') : 0xeace; // TODO: We don't use AsyncMode or ConcurrentMode anymore. They were temporary
	// (unstable) APIs that have been removed. Can we remove the symbols?

	var REACT_ASYNC_MODE_TYPE = hasSymbol ? Symbol.for('react.async_mode') : 0xeacf;
	var REACT_CONCURRENT_MODE_TYPE = hasSymbol ? Symbol.for('react.concurrent_mode') : 0xeacf;
	var REACT_FORWARD_REF_TYPE = hasSymbol ? Symbol.for('react.forward_ref') : 0xead0;
	var REACT_SUSPENSE_TYPE = hasSymbol ? Symbol.for('react.suspense') : 0xead1;
	var REACT_SUSPENSE_LIST_TYPE = hasSymbol ? Symbol.for('react.suspense_list') : 0xead8;
	var REACT_MEMO_TYPE = hasSymbol ? Symbol.for('react.memo') : 0xead3;
	var REACT_LAZY_TYPE = hasSymbol ? Symbol.for('react.lazy') : 0xead4;
	var REACT_BLOCK_TYPE = hasSymbol ? Symbol.for('react.block') : 0xead9;
	var REACT_FUNDAMENTAL_TYPE = hasSymbol ? Symbol.for('react.fundamental') : 0xead5;
	var REACT_RESPONDER_TYPE = hasSymbol ? Symbol.for('react.responder') : 0xead6;
	var REACT_SCOPE_TYPE = hasSymbol ? Symbol.for('react.scope') : 0xead7;

	function isValidElementType(type) {
	  return typeof type === 'string' || typeof type === 'function' || // Note: its typeof might be other than 'symbol' or 'number' if it's a polyfill.
	  type === REACT_FRAGMENT_TYPE || type === REACT_CONCURRENT_MODE_TYPE || type === REACT_PROFILER_TYPE || type === REACT_STRICT_MODE_TYPE || type === REACT_SUSPENSE_TYPE || type === REACT_SUSPENSE_LIST_TYPE || typeof type === 'object' && type !== null && (type.$$typeof === REACT_LAZY_TYPE || type.$$typeof === REACT_MEMO_TYPE || type.$$typeof === REACT_PROVIDER_TYPE || type.$$typeof === REACT_CONTEXT_TYPE || type.$$typeof === REACT_FORWARD_REF_TYPE || type.$$typeof === REACT_FUNDAMENTAL_TYPE || type.$$typeof === REACT_RESPONDER_TYPE || type.$$typeof === REACT_SCOPE_TYPE || type.$$typeof === REACT_BLOCK_TYPE);
	}

	function typeOf(object) {
	  if (typeof object === 'object' && object !== null) {
	    var $$typeof = object.$$typeof;

	    switch ($$typeof) {
	      case REACT_ELEMENT_TYPE:
	        var type = object.type;

	        switch (type) {
	          case REACT_ASYNC_MODE_TYPE:
	          case REACT_CONCURRENT_MODE_TYPE:
	          case REACT_FRAGMENT_TYPE:
	          case REACT_PROFILER_TYPE:
	          case REACT_STRICT_MODE_TYPE:
	          case REACT_SUSPENSE_TYPE:
	            return type;

	          default:
	            var $$typeofType = type && type.$$typeof;

	            switch ($$typeofType) {
	              case REACT_CONTEXT_TYPE:
	              case REACT_FORWARD_REF_TYPE:
	              case REACT_LAZY_TYPE:
	              case REACT_MEMO_TYPE:
	              case REACT_PROVIDER_TYPE:
	                return $$typeofType;

	              default:
	                return $$typeof;
	            }

	        }

	      case REACT_PORTAL_TYPE:
	        return $$typeof;
	    }
	  }

	  return undefined;
	} // AsyncMode is deprecated along with isAsyncMode

	var AsyncMode = REACT_ASYNC_MODE_TYPE;
	var ConcurrentMode = REACT_CONCURRENT_MODE_TYPE;
	var ContextConsumer = REACT_CONTEXT_TYPE;
	var ContextProvider = REACT_PROVIDER_TYPE;
	var Element = REACT_ELEMENT_TYPE;
	var ForwardRef = REACT_FORWARD_REF_TYPE;
	var Fragment = REACT_FRAGMENT_TYPE;
	var Lazy = REACT_LAZY_TYPE;
	var Memo = REACT_MEMO_TYPE;
	var Portal = REACT_PORTAL_TYPE;
	var Profiler = REACT_PROFILER_TYPE;
	var StrictMode = REACT_STRICT_MODE_TYPE;
	var Suspense = REACT_SUSPENSE_TYPE;
	var hasWarnedAboutDeprecatedIsAsyncMode = false; // AsyncMode should be deprecated

	function isAsyncMode(object) {
	  {
	    if (!hasWarnedAboutDeprecatedIsAsyncMode) {
	      hasWarnedAboutDeprecatedIsAsyncMode = true; // Using console['warn'] to evade Babel and ESLint

	      console['warn']('The ReactIs.isAsyncMode() alias has been deprecated, ' + 'and will be removed in React 17+. Update your code to use ' + 'ReactIs.isConcurrentMode() instead. It has the exact same API.');
	    }
	  }

	  return isConcurrentMode(object) || typeOf(object) === REACT_ASYNC_MODE_TYPE;
	}
	function isConcurrentMode(object) {
	  return typeOf(object) === REACT_CONCURRENT_MODE_TYPE;
	}
	function isContextConsumer(object) {
	  return typeOf(object) === REACT_CONTEXT_TYPE;
	}
	function isContextProvider(object) {
	  return typeOf(object) === REACT_PROVIDER_TYPE;
	}
	function isElement(object) {
	  return typeof object === 'object' && object !== null && object.$$typeof === REACT_ELEMENT_TYPE;
	}
	function isForwardRef(object) {
	  return typeOf(object) === REACT_FORWARD_REF_TYPE;
	}
	function isFragment(object) {
	  return typeOf(object) === REACT_FRAGMENT_TYPE;
	}
	function isLazy(object) {
	  return typeOf(object) === REACT_LAZY_TYPE;
	}
	function isMemo(object) {
	  return typeOf(object) === REACT_MEMO_TYPE;
	}
	function isPortal(object) {
	  return typeOf(object) === REACT_PORTAL_TYPE;
	}
	function isProfiler(object) {
	  return typeOf(object) === REACT_PROFILER_TYPE;
	}
	function isStrictMode(object) {
	  return typeOf(object) === REACT_STRICT_MODE_TYPE;
	}
	function isSuspense(object) {
	  return typeOf(object) === REACT_SUSPENSE_TYPE;
	}

	reactIs_development$1.AsyncMode = AsyncMode;
	reactIs_development$1.ConcurrentMode = ConcurrentMode;
	reactIs_development$1.ContextConsumer = ContextConsumer;
	reactIs_development$1.ContextProvider = ContextProvider;
	reactIs_development$1.Element = Element;
	reactIs_development$1.ForwardRef = ForwardRef;
	reactIs_development$1.Fragment = Fragment;
	reactIs_development$1.Lazy = Lazy;
	reactIs_development$1.Memo = Memo;
	reactIs_development$1.Portal = Portal;
	reactIs_development$1.Profiler = Profiler;
	reactIs_development$1.StrictMode = StrictMode;
	reactIs_development$1.Suspense = Suspense;
	reactIs_development$1.isAsyncMode = isAsyncMode;
	reactIs_development$1.isConcurrentMode = isConcurrentMode;
	reactIs_development$1.isContextConsumer = isContextConsumer;
	reactIs_development$1.isContextProvider = isContextProvider;
	reactIs_development$1.isElement = isElement;
	reactIs_development$1.isForwardRef = isForwardRef;
	reactIs_development$1.isFragment = isFragment;
	reactIs_development$1.isLazy = isLazy;
	reactIs_development$1.isMemo = isMemo;
	reactIs_development$1.isPortal = isPortal;
	reactIs_development$1.isProfiler = isProfiler;
	reactIs_development$1.isStrictMode = isStrictMode;
	reactIs_development$1.isSuspense = isSuspense;
	reactIs_development$1.isValidElementType = isValidElementType;
	reactIs_development$1.typeOf = typeOf;
	  })();
	}
	return reactIs_development$1;
}

var hasRequiredReactIs$1;

function requireReactIs$1 () {
	if (hasRequiredReactIs$1) return reactIs$1.exports;
	hasRequiredReactIs$1 = 1;

	if (process.env.NODE_ENV === 'production') {
	  reactIs$1.exports = requireReactIs_production_min$1();
	} else {
	  reactIs$1.exports = requireReactIs_development$1();
	}
	return reactIs$1.exports;
}

/*
object-assign
(c) Sindre Sorhus
@license MIT
*/

var objectAssign$1;
var hasRequiredObjectAssign$1;

function requireObjectAssign$1 () {
	if (hasRequiredObjectAssign$1) return objectAssign$1;
	hasRequiredObjectAssign$1 = 1;
	/* eslint-disable no-unused-vars */
	var getOwnPropertySymbols = Object.getOwnPropertySymbols;
	var hasOwnProperty = Object.prototype.hasOwnProperty;
	var propIsEnumerable = Object.prototype.propertyIsEnumerable;

	function toObject(val) {
		if (val === null || val === undefined) {
			throw new TypeError('Object.assign cannot be called with null or undefined');
		}

		return Object(val);
	}

	function shouldUseNative() {
		try {
			if (!Object.assign) {
				return false;
			}

			// Detect buggy property enumeration order in older V8 versions.

			// https://bugs.chromium.org/p/v8/issues/detail?id=4118
			var test1 = new String('abc');  // eslint-disable-line no-new-wrappers
			test1[5] = 'de';
			if (Object.getOwnPropertyNames(test1)[0] === '5') {
				return false;
			}

			// https://bugs.chromium.org/p/v8/issues/detail?id=3056
			var test2 = {};
			for (var i = 0; i < 10; i++) {
				test2['_' + String.fromCharCode(i)] = i;
			}
			var order2 = Object.getOwnPropertyNames(test2).map(function (n) {
				return test2[n];
			});
			if (order2.join('') !== '0123456789') {
				return false;
			}

			// https://bugs.chromium.org/p/v8/issues/detail?id=3056
			var test3 = {};
			'abcdefghijklmnopqrst'.split('').forEach(function (letter) {
				test3[letter] = letter;
			});
			if (Object.keys(Object.assign({}, test3)).join('') !==
					'abcdefghijklmnopqrst') {
				return false;
			}

			return true;
		} catch (err) {
			// We don't expect any of the above to throw, but better to be safe.
			return false;
		}
	}

	objectAssign$1 = shouldUseNative() ? Object.assign : function (target, source) {
		var from;
		var to = toObject(target);
		var symbols;

		for (var s = 1; s < arguments.length; s++) {
			from = Object(arguments[s]);

			for (var key in from) {
				if (hasOwnProperty.call(from, key)) {
					to[key] = from[key];
				}
			}

			if (getOwnPropertySymbols) {
				symbols = getOwnPropertySymbols(from);
				for (var i = 0; i < symbols.length; i++) {
					if (propIsEnumerable.call(from, symbols[i])) {
						to[symbols[i]] = from[symbols[i]];
					}
				}
			}
		}

		return to;
	};
	return objectAssign$1;
}

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

var ReactPropTypesSecret_1$1;
var hasRequiredReactPropTypesSecret$1;

function requireReactPropTypesSecret$1 () {
	if (hasRequiredReactPropTypesSecret$1) return ReactPropTypesSecret_1$1;
	hasRequiredReactPropTypesSecret$1 = 1;

	var ReactPropTypesSecret = 'SECRET_DO_NOT_PASS_THIS_OR_YOU_WILL_BE_FIRED';

	ReactPropTypesSecret_1$1 = ReactPropTypesSecret;
	return ReactPropTypesSecret_1$1;
}

var has$1;
var hasRequiredHas$1;

function requireHas$1 () {
	if (hasRequiredHas$1) return has$1;
	hasRequiredHas$1 = 1;
	has$1 = Function.call.bind(Object.prototype.hasOwnProperty);
	return has$1;
}

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

var checkPropTypes_1$1;
var hasRequiredCheckPropTypes$1;

function requireCheckPropTypes$1 () {
	if (hasRequiredCheckPropTypes$1) return checkPropTypes_1$1;
	hasRequiredCheckPropTypes$1 = 1;

	var printWarning = function() {};

	if (process.env.NODE_ENV !== 'production') {
	  var ReactPropTypesSecret = requireReactPropTypesSecret$1();
	  var loggedTypeFailures = {};
	  var has = requireHas$1();

	  printWarning = function(text) {
	    var message = 'Warning: ' + text;
	    if (typeof console !== 'undefined') {
	      console.error(message);
	    }
	    try {
	      // --- Welcome to debugging React ---
	      // This error was thrown as a convenience so that you can use this stack
	      // to find the callsite that caused this warning to fire.
	      throw new Error(message);
	    } catch (x) { /**/ }
	  };
	}

	/**
	 * Assert that the values match with the type specs.
	 * Error messages are memorized and will only be shown once.
	 *
	 * @param {object} typeSpecs Map of name to a ReactPropType
	 * @param {object} values Runtime values that need to be type-checked
	 * @param {string} location e.g. "prop", "context", "child context"
	 * @param {string} componentName Name of the component for error messages.
	 * @param {?Function} getStack Returns the component stack.
	 * @private
	 */
	function checkPropTypes(typeSpecs, values, location, componentName, getStack) {
	  if (process.env.NODE_ENV !== 'production') {
	    for (var typeSpecName in typeSpecs) {
	      if (has(typeSpecs, typeSpecName)) {
	        var error;
	        // Prop type validation may throw. In case they do, we don't want to
	        // fail the render phase where it didn't fail before. So we log it.
	        // After these have been cleaned up, we'll let them throw.
	        try {
	          // This is intentionally an invariant that gets caught. It's the same
	          // behavior as without this statement except with a better message.
	          if (typeof typeSpecs[typeSpecName] !== 'function') {
	            var err = Error(
	              (componentName || 'React class') + ': ' + location + ' type `' + typeSpecName + '` is invalid; ' +
	              'it must be a function, usually from the `prop-types` package, but received `' + typeof typeSpecs[typeSpecName] + '`.' +
	              'This often happens because of typos such as `PropTypes.function` instead of `PropTypes.func`.'
	            );
	            err.name = 'Invariant Violation';
	            throw err;
	          }
	          error = typeSpecs[typeSpecName](values, typeSpecName, componentName, location, null, ReactPropTypesSecret);
	        } catch (ex) {
	          error = ex;
	        }
	        if (error && !(error instanceof Error)) {
	          printWarning(
	            (componentName || 'React class') + ': type specification of ' +
	            location + ' `' + typeSpecName + '` is invalid; the type checker ' +
	            'function must return `null` or an `Error` but returned a ' + typeof error + '. ' +
	            'You may have forgotten to pass an argument to the type checker ' +
	            'creator (arrayOf, instanceOf, objectOf, oneOf, oneOfType, and ' +
	            'shape all require an argument).'
	          );
	        }
	        if (error instanceof Error && !(error.message in loggedTypeFailures)) {
	          // Only monitor this failure once because there tends to be a lot of the
	          // same error.
	          loggedTypeFailures[error.message] = true;

	          var stack = getStack ? getStack() : '';

	          printWarning(
	            'Failed ' + location + ' type: ' + error.message + (stack != null ? stack : '')
	          );
	        }
	      }
	    }
	  }
	}

	/**
	 * Resets warning cache when testing.
	 *
	 * @private
	 */
	checkPropTypes.resetWarningCache = function() {
	  if (process.env.NODE_ENV !== 'production') {
	    loggedTypeFailures = {};
	  }
	};

	checkPropTypes_1$1 = checkPropTypes;
	return checkPropTypes_1$1;
}

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

var factoryWithTypeCheckers$1;
var hasRequiredFactoryWithTypeCheckers$1;

function requireFactoryWithTypeCheckers$1 () {
	if (hasRequiredFactoryWithTypeCheckers$1) return factoryWithTypeCheckers$1;
	hasRequiredFactoryWithTypeCheckers$1 = 1;

	var ReactIs = requireReactIs$1();
	var assign = requireObjectAssign$1();

	var ReactPropTypesSecret = requireReactPropTypesSecret$1();
	var has = requireHas$1();
	var checkPropTypes = requireCheckPropTypes$1();

	var printWarning = function() {};

	if (process.env.NODE_ENV !== 'production') {
	  printWarning = function(text) {
	    var message = 'Warning: ' + text;
	    if (typeof console !== 'undefined') {
	      console.error(message);
	    }
	    try {
	      // --- Welcome to debugging React ---
	      // This error was thrown as a convenience so that you can use this stack
	      // to find the callsite that caused this warning to fire.
	      throw new Error(message);
	    } catch (x) {}
	  };
	}

	function emptyFunctionThatReturnsNull() {
	  return null;
	}

	factoryWithTypeCheckers$1 = function(isValidElement, throwOnDirectAccess) {
	  /* global Symbol */
	  var ITERATOR_SYMBOL = typeof Symbol === 'function' && Symbol.iterator;
	  var FAUX_ITERATOR_SYMBOL = '@@iterator'; // Before Symbol spec.

	  /**
	   * Returns the iterator method function contained on the iterable object.
	   *
	   * Be sure to invoke the function with the iterable as context:
	   *
	   *     var iteratorFn = getIteratorFn(myIterable);
	   *     if (iteratorFn) {
	   *       var iterator = iteratorFn.call(myIterable);
	   *       ...
	   *     }
	   *
	   * @param {?object} maybeIterable
	   * @return {?function}
	   */
	  function getIteratorFn(maybeIterable) {
	    var iteratorFn = maybeIterable && (ITERATOR_SYMBOL && maybeIterable[ITERATOR_SYMBOL] || maybeIterable[FAUX_ITERATOR_SYMBOL]);
	    if (typeof iteratorFn === 'function') {
	      return iteratorFn;
	    }
	  }

	  /**
	   * Collection of methods that allow declaration and validation of props that are
	   * supplied to React components. Example usage:
	   *
	   *   var Props = require('ReactPropTypes');
	   *   var MyArticle = React.createClass({
	   *     propTypes: {
	   *       // An optional string prop named "description".
	   *       description: Props.string,
	   *
	   *       // A required enum prop named "category".
	   *       category: Props.oneOf(['News','Photos']).isRequired,
	   *
	   *       // A prop named "dialog" that requires an instance of Dialog.
	   *       dialog: Props.instanceOf(Dialog).isRequired
	   *     },
	   *     render: function() { ... }
	   *   });
	   *
	   * A more formal specification of how these methods are used:
	   *
	   *   type := array|bool|func|object|number|string|oneOf([...])|instanceOf(...)
	   *   decl := ReactPropTypes.{type}(.isRequired)?
	   *
	   * Each and every declaration produces a function with the same signature. This
	   * allows the creation of custom validation functions. For example:
	   *
	   *  var MyLink = React.createClass({
	   *    propTypes: {
	   *      // An optional string or URI prop named "href".
	   *      href: function(props, propName, componentName) {
	   *        var propValue = props[propName];
	   *        if (propValue != null && typeof propValue !== 'string' &&
	   *            !(propValue instanceof URI)) {
	   *          return new Error(
	   *            'Expected a string or an URI for ' + propName + ' in ' +
	   *            componentName
	   *          );
	   *        }
	   *      }
	   *    },
	   *    render: function() {...}
	   *  });
	   *
	   * @internal
	   */

	  var ANONYMOUS = '<<anonymous>>';

	  // Important!
	  // Keep this list in sync with production version in `./factoryWithThrowingShims.js`.
	  var ReactPropTypes = {
	    array: createPrimitiveTypeChecker('array'),
	    bigint: createPrimitiveTypeChecker('bigint'),
	    bool: createPrimitiveTypeChecker('boolean'),
	    func: createPrimitiveTypeChecker('function'),
	    number: createPrimitiveTypeChecker('number'),
	    object: createPrimitiveTypeChecker('object'),
	    string: createPrimitiveTypeChecker('string'),
	    symbol: createPrimitiveTypeChecker('symbol'),

	    any: createAnyTypeChecker(),
	    arrayOf: createArrayOfTypeChecker,
	    element: createElementTypeChecker(),
	    elementType: createElementTypeTypeChecker(),
	    instanceOf: createInstanceTypeChecker,
	    node: createNodeChecker(),
	    objectOf: createObjectOfTypeChecker,
	    oneOf: createEnumTypeChecker,
	    oneOfType: createUnionTypeChecker,
	    shape: createShapeTypeChecker,
	    exact: createStrictShapeTypeChecker,
	  };

	  /**
	   * inlined Object.is polyfill to avoid requiring consumers ship their own
	   * https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Object/is
	   */
	  /*eslint-disable no-self-compare*/
	  function is(x, y) {
	    // SameValue algorithm
	    if (x === y) {
	      // Steps 1-5, 7-10
	      // Steps 6.b-6.e: +0 != -0
	      return x !== 0 || 1 / x === 1 / y;
	    } else {
	      // Step 6.a: NaN == NaN
	      return x !== x && y !== y;
	    }
	  }
	  /*eslint-enable no-self-compare*/

	  /**
	   * We use an Error-like object for backward compatibility as people may call
	   * PropTypes directly and inspect their output. However, we don't use real
	   * Errors anymore. We don't inspect their stack anyway, and creating them
	   * is prohibitively expensive if they are created too often, such as what
	   * happens in oneOfType() for any type before the one that matched.
	   */
	  function PropTypeError(message, data) {
	    this.message = message;
	    this.data = data && typeof data === 'object' ? data: {};
	    this.stack = '';
	  }
	  // Make `instanceof Error` still work for returned errors.
	  PropTypeError.prototype = Error.prototype;

	  function createChainableTypeChecker(validate) {
	    if (process.env.NODE_ENV !== 'production') {
	      var manualPropTypeCallCache = {};
	      var manualPropTypeWarningCount = 0;
	    }
	    function checkType(isRequired, props, propName, componentName, location, propFullName, secret) {
	      componentName = componentName || ANONYMOUS;
	      propFullName = propFullName || propName;

	      if (secret !== ReactPropTypesSecret) {
	        if (throwOnDirectAccess) {
	          // New behavior only for users of `prop-types` package
	          var err = new Error(
	            'Calling PropTypes validators directly is not supported by the `prop-types` package. ' +
	            'Use `PropTypes.checkPropTypes()` to call them. ' +
	            'Read more at http://fb.me/use-check-prop-types'
	          );
	          err.name = 'Invariant Violation';
	          throw err;
	        } else if (process.env.NODE_ENV !== 'production' && typeof console !== 'undefined') {
	          // Old behavior for people using React.PropTypes
	          var cacheKey = componentName + ':' + propName;
	          if (
	            !manualPropTypeCallCache[cacheKey] &&
	            // Avoid spamming the console because they are often not actionable except for lib authors
	            manualPropTypeWarningCount < 3
	          ) {
	            printWarning(
	              'You are manually calling a React.PropTypes validation ' +
	              'function for the `' + propFullName + '` prop on `' + componentName + '`. This is deprecated ' +
	              'and will throw in the standalone `prop-types` package. ' +
	              'You may be seeing this warning due to a third-party PropTypes ' +
	              'library. See https://fb.me/react-warning-dont-call-proptypes ' + 'for details.'
	            );
	            manualPropTypeCallCache[cacheKey] = true;
	            manualPropTypeWarningCount++;
	          }
	        }
	      }
	      if (props[propName] == null) {
	        if (isRequired) {
	          if (props[propName] === null) {
	            return new PropTypeError('The ' + location + ' `' + propFullName + '` is marked as required ' + ('in `' + componentName + '`, but its value is `null`.'));
	          }
	          return new PropTypeError('The ' + location + ' `' + propFullName + '` is marked as required in ' + ('`' + componentName + '`, but its value is `undefined`.'));
	        }
	        return null;
	      } else {
	        return validate(props, propName, componentName, location, propFullName);
	      }
	    }

	    var chainedCheckType = checkType.bind(null, false);
	    chainedCheckType.isRequired = checkType.bind(null, true);

	    return chainedCheckType;
	  }

	  function createPrimitiveTypeChecker(expectedType) {
	    function validate(props, propName, componentName, location, propFullName, secret) {
	      var propValue = props[propName];
	      var propType = getPropType(propValue);
	      if (propType !== expectedType) {
	        // `propValue` being instance of, say, date/regexp, pass the 'object'
	        // check, but we can offer a more precise error message here rather than
	        // 'of type `object`'.
	        var preciseType = getPreciseType(propValue);

	        return new PropTypeError(
	          'Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + preciseType + '` supplied to `' + componentName + '`, expected ') + ('`' + expectedType + '`.'),
	          {expectedType: expectedType}
	        );
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createAnyTypeChecker() {
	    return createChainableTypeChecker(emptyFunctionThatReturnsNull);
	  }

	  function createArrayOfTypeChecker(typeChecker) {
	    function validate(props, propName, componentName, location, propFullName) {
	      if (typeof typeChecker !== 'function') {
	        return new PropTypeError('Property `' + propFullName + '` of component `' + componentName + '` has invalid PropType notation inside arrayOf.');
	      }
	      var propValue = props[propName];
	      if (!Array.isArray(propValue)) {
	        var propType = getPropType(propValue);
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected an array.'));
	      }
	      for (var i = 0; i < propValue.length; i++) {
	        var error = typeChecker(propValue, i, componentName, location, propFullName + '[' + i + ']', ReactPropTypesSecret);
	        if (error instanceof Error) {
	          return error;
	        }
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createElementTypeChecker() {
	    function validate(props, propName, componentName, location, propFullName) {
	      var propValue = props[propName];
	      if (!isValidElement(propValue)) {
	        var propType = getPropType(propValue);
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected a single ReactElement.'));
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createElementTypeTypeChecker() {
	    function validate(props, propName, componentName, location, propFullName) {
	      var propValue = props[propName];
	      if (!ReactIs.isValidElementType(propValue)) {
	        var propType = getPropType(propValue);
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected a single ReactElement type.'));
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createInstanceTypeChecker(expectedClass) {
	    function validate(props, propName, componentName, location, propFullName) {
	      if (!(props[propName] instanceof expectedClass)) {
	        var expectedClassName = expectedClass.name || ANONYMOUS;
	        var actualClassName = getClassName(props[propName]);
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + actualClassName + '` supplied to `' + componentName + '`, expected ') + ('instance of `' + expectedClassName + '`.'));
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createEnumTypeChecker(expectedValues) {
	    if (!Array.isArray(expectedValues)) {
	      if (process.env.NODE_ENV !== 'production') {
	        if (arguments.length > 1) {
	          printWarning(
	            'Invalid arguments supplied to oneOf, expected an array, got ' + arguments.length + ' arguments. ' +
	            'A common mistake is to write oneOf(x, y, z) instead of oneOf([x, y, z]).'
	          );
	        } else {
	          printWarning('Invalid argument supplied to oneOf, expected an array.');
	        }
	      }
	      return emptyFunctionThatReturnsNull;
	    }

	    function validate(props, propName, componentName, location, propFullName) {
	      var propValue = props[propName];
	      for (var i = 0; i < expectedValues.length; i++) {
	        if (is(propValue, expectedValues[i])) {
	          return null;
	        }
	      }

	      var valuesString = JSON.stringify(expectedValues, function replacer(key, value) {
	        var type = getPreciseType(value);
	        if (type === 'symbol') {
	          return String(value);
	        }
	        return value;
	      });
	      return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of value `' + String(propValue) + '` ' + ('supplied to `' + componentName + '`, expected one of ' + valuesString + '.'));
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createObjectOfTypeChecker(typeChecker) {
	    function validate(props, propName, componentName, location, propFullName) {
	      if (typeof typeChecker !== 'function') {
	        return new PropTypeError('Property `' + propFullName + '` of component `' + componentName + '` has invalid PropType notation inside objectOf.');
	      }
	      var propValue = props[propName];
	      var propType = getPropType(propValue);
	      if (propType !== 'object') {
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected an object.'));
	      }
	      for (var key in propValue) {
	        if (has(propValue, key)) {
	          var error = typeChecker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret);
	          if (error instanceof Error) {
	            return error;
	          }
	        }
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createUnionTypeChecker(arrayOfTypeCheckers) {
	    if (!Array.isArray(arrayOfTypeCheckers)) {
	      process.env.NODE_ENV !== 'production' ? printWarning('Invalid argument supplied to oneOfType, expected an instance of array.') : void 0;
	      return emptyFunctionThatReturnsNull;
	    }

	    for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
	      var checker = arrayOfTypeCheckers[i];
	      if (typeof checker !== 'function') {
	        printWarning(
	          'Invalid argument supplied to oneOfType. Expected an array of check functions, but ' +
	          'received ' + getPostfixForTypeWarning(checker) + ' at index ' + i + '.'
	        );
	        return emptyFunctionThatReturnsNull;
	      }
	    }

	    function validate(props, propName, componentName, location, propFullName) {
	      var expectedTypes = [];
	      for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
	        var checker = arrayOfTypeCheckers[i];
	        var checkerResult = checker(props, propName, componentName, location, propFullName, ReactPropTypesSecret);
	        if (checkerResult == null) {
	          return null;
	        }
	        if (checkerResult.data && has(checkerResult.data, 'expectedType')) {
	          expectedTypes.push(checkerResult.data.expectedType);
	        }
	      }
	      var expectedTypesMessage = (expectedTypes.length > 0) ? ', expected one of type [' + expectedTypes.join(', ') + ']': '';
	      return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` supplied to ' + ('`' + componentName + '`' + expectedTypesMessage + '.'));
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createNodeChecker() {
	    function validate(props, propName, componentName, location, propFullName) {
	      if (!isNode(props[propName])) {
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` supplied to ' + ('`' + componentName + '`, expected a ReactNode.'));
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function invalidValidatorError(componentName, location, propFullName, key, type) {
	    return new PropTypeError(
	      (componentName || 'React class') + ': ' + location + ' type `' + propFullName + '.' + key + '` is invalid; ' +
	      'it must be a function, usually from the `prop-types` package, but received `' + type + '`.'
	    );
	  }

	  function createShapeTypeChecker(shapeTypes) {
	    function validate(props, propName, componentName, location, propFullName) {
	      var propValue = props[propName];
	      var propType = getPropType(propValue);
	      if (propType !== 'object') {
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type `' + propType + '` ' + ('supplied to `' + componentName + '`, expected `object`.'));
	      }
	      for (var key in shapeTypes) {
	        var checker = shapeTypes[key];
	        if (typeof checker !== 'function') {
	          return invalidValidatorError(componentName, location, propFullName, key, getPreciseType(checker));
	        }
	        var error = checker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret);
	        if (error) {
	          return error;
	        }
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createStrictShapeTypeChecker(shapeTypes) {
	    function validate(props, propName, componentName, location, propFullName) {
	      var propValue = props[propName];
	      var propType = getPropType(propValue);
	      if (propType !== 'object') {
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type `' + propType + '` ' + ('supplied to `' + componentName + '`, expected `object`.'));
	      }
	      // We need to check all keys in case some are required but missing from props.
	      var allKeys = assign({}, props[propName], shapeTypes);
	      for (var key in allKeys) {
	        var checker = shapeTypes[key];
	        if (has(shapeTypes, key) && typeof checker !== 'function') {
	          return invalidValidatorError(componentName, location, propFullName, key, getPreciseType(checker));
	        }
	        if (!checker) {
	          return new PropTypeError(
	            'Invalid ' + location + ' `' + propFullName + '` key `' + key + '` supplied to `' + componentName + '`.' +
	            '\nBad object: ' + JSON.stringify(props[propName], null, '  ') +
	            '\nValid keys: ' + JSON.stringify(Object.keys(shapeTypes), null, '  ')
	          );
	        }
	        var error = checker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret);
	        if (error) {
	          return error;
	        }
	      }
	      return null;
	    }

	    return createChainableTypeChecker(validate);
	  }

	  function isNode(propValue) {
	    switch (typeof propValue) {
	      case 'number':
	      case 'string':
	      case 'undefined':
	        return true;
	      case 'boolean':
	        return !propValue;
	      case 'object':
	        if (Array.isArray(propValue)) {
	          return propValue.every(isNode);
	        }
	        if (propValue === null || isValidElement(propValue)) {
	          return true;
	        }

	        var iteratorFn = getIteratorFn(propValue);
	        if (iteratorFn) {
	          var iterator = iteratorFn.call(propValue);
	          var step;
	          if (iteratorFn !== propValue.entries) {
	            while (!(step = iterator.next()).done) {
	              if (!isNode(step.value)) {
	                return false;
	              }
	            }
	          } else {
	            // Iterator will provide entry [k,v] tuples rather than values.
	            while (!(step = iterator.next()).done) {
	              var entry = step.value;
	              if (entry) {
	                if (!isNode(entry[1])) {
	                  return false;
	                }
	              }
	            }
	          }
	        } else {
	          return false;
	        }

	        return true;
	      default:
	        return false;
	    }
	  }

	  function isSymbol(propType, propValue) {
	    // Native Symbol.
	    if (propType === 'symbol') {
	      return true;
	    }

	    // falsy value can't be a Symbol
	    if (!propValue) {
	      return false;
	    }

	    // 19.4.3.5 Symbol.prototype[@@toStringTag] === 'Symbol'
	    if (propValue['@@toStringTag'] === 'Symbol') {
	      return true;
	    }

	    // Fallback for non-spec compliant Symbols which are polyfilled.
	    if (typeof Symbol === 'function' && propValue instanceof Symbol) {
	      return true;
	    }

	    return false;
	  }

	  // Equivalent of `typeof` but with special handling for array and regexp.
	  function getPropType(propValue) {
	    var propType = typeof propValue;
	    if (Array.isArray(propValue)) {
	      return 'array';
	    }
	    if (propValue instanceof RegExp) {
	      // Old webkits (at least until Android 4.0) return 'function' rather than
	      // 'object' for typeof a RegExp. We'll normalize this here so that /bla/
	      // passes PropTypes.object.
	      return 'object';
	    }
	    if (isSymbol(propType, propValue)) {
	      return 'symbol';
	    }
	    return propType;
	  }

	  // This handles more types than `getPropType`. Only used for error messages.
	  // See `createPrimitiveTypeChecker`.
	  function getPreciseType(propValue) {
	    if (typeof propValue === 'undefined' || propValue === null) {
	      return '' + propValue;
	    }
	    var propType = getPropType(propValue);
	    if (propType === 'object') {
	      if (propValue instanceof Date) {
	        return 'date';
	      } else if (propValue instanceof RegExp) {
	        return 'regexp';
	      }
	    }
	    return propType;
	  }

	  // Returns a string that is postfixed to a warning about an invalid type.
	  // For example, "undefined" or "of type array"
	  function getPostfixForTypeWarning(value) {
	    var type = getPreciseType(value);
	    switch (type) {
	      case 'array':
	      case 'object':
	        return 'an ' + type;
	      case 'boolean':
	      case 'date':
	      case 'regexp':
	        return 'a ' + type;
	      default:
	        return type;
	    }
	  }

	  // Returns class name of the object, if any.
	  function getClassName(propValue) {
	    if (!propValue.constructor || !propValue.constructor.name) {
	      return ANONYMOUS;
	    }
	    return propValue.constructor.name;
	  }

	  ReactPropTypes.checkPropTypes = checkPropTypes;
	  ReactPropTypes.resetWarningCache = checkPropTypes.resetWarningCache;
	  ReactPropTypes.PropTypes = ReactPropTypes;

	  return ReactPropTypes;
	};
	return factoryWithTypeCheckers$1;
}

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

var factoryWithThrowingShims$1;
var hasRequiredFactoryWithThrowingShims$1;

function requireFactoryWithThrowingShims$1 () {
	if (hasRequiredFactoryWithThrowingShims$1) return factoryWithThrowingShims$1;
	hasRequiredFactoryWithThrowingShims$1 = 1;

	var ReactPropTypesSecret = requireReactPropTypesSecret$1();

	function emptyFunction() {}
	function emptyFunctionWithReset() {}
	emptyFunctionWithReset.resetWarningCache = emptyFunction;

	factoryWithThrowingShims$1 = function() {
	  function shim(props, propName, componentName, location, propFullName, secret) {
	    if (secret === ReactPropTypesSecret) {
	      // It is still safe when called from React.
	      return;
	    }
	    var err = new Error(
	      'Calling PropTypes validators directly is not supported by the `prop-types` package. ' +
	      'Use PropTypes.checkPropTypes() to call them. ' +
	      'Read more at http://fb.me/use-check-prop-types'
	    );
	    err.name = 'Invariant Violation';
	    throw err;
	  }	  shim.isRequired = shim;
	  function getShim() {
	    return shim;
	  }	  // Important!
	  // Keep this list in sync with production version in `./factoryWithTypeCheckers.js`.
	  var ReactPropTypes = {
	    array: shim,
	    bigint: shim,
	    bool: shim,
	    func: shim,
	    number: shim,
	    object: shim,
	    string: shim,
	    symbol: shim,

	    any: shim,
	    arrayOf: getShim,
	    element: shim,
	    elementType: shim,
	    instanceOf: getShim,
	    node: shim,
	    objectOf: getShim,
	    oneOf: getShim,
	    oneOfType: getShim,
	    shape: getShim,
	    exact: getShim,

	    checkPropTypes: emptyFunctionWithReset,
	    resetWarningCache: emptyFunction
	  };

	  ReactPropTypes.PropTypes = ReactPropTypes;

	  return ReactPropTypes;
	};
	return factoryWithThrowingShims$1;
}

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

if (process.env.NODE_ENV !== 'production') {
  var ReactIs$1 = requireReactIs$1();

  // By explicitly using `prop-types` you are opting into new development behavior.
  // http://fb.me/prop-types-in-prod
  var throwOnDirectAccess$1 = true;
  propTypes$1.exports = requireFactoryWithTypeCheckers$1()(ReactIs$1.isElement, throwOnDirectAccess$1);
} else {
  // By explicitly using `prop-types` you are opting into new production behavior.
  // http://fb.me/prop-types-in-prod
  propTypes$1.exports = requireFactoryWithThrowingShims$1()();
}

var propTypesExports$1 = propTypes$1.exports;
var PropTypes$1 = /*@__PURE__*/getDefaultExportFromCjs$1(propTypesExports$1);

var classnames$1 = {exports: {}};

/*!
	Copyright (c) 2018 Jed Watson.
	Licensed under the MIT License (MIT), see
	http://jedwatson.github.io/classnames
*/

(function (module) {
	/* global define */

	(function () {

		var hasOwn = {}.hasOwnProperty;

		function classNames() {
			var classes = [];

			for (var i = 0; i < arguments.length; i++) {
				var arg = arguments[i];
				if (!arg) continue;

				var argType = typeof arg;

				if (argType === 'string' || argType === 'number') {
					classes.push(arg);
				} else if (Array.isArray(arg)) {
					if (arg.length) {
						var inner = classNames.apply(null, arg);
						if (inner) {
							classes.push(inner);
						}
					}
				} else if (argType === 'object') {
					if (arg.toString !== Object.prototype.toString && !arg.toString.toString().includes('[native code]')) {
						classes.push(arg.toString());
						continue;
					}

					for (var key in arg) {
						if (hasOwn.call(arg, key) && arg[key]) {
							classes.push(key);
						}
					}
				}
			}

			return classes.join(' ');
		}

		if (module.exports) {
			classNames.default = classNames;
			module.exports = classNames;
		} else {
			window.classNames = classNames;
		}
	}()); 
} (classnames$1));

var classnamesExports$1 = classnames$1.exports;
var classNames$1 = /*@__PURE__*/getDefaultExportFromCjs$1(classnamesExports$1);

var CAccordionContext = React$1.createContext({});
var CAccordion = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, activeItemKey = _a.activeItemKey, _b = _a.alwaysOpen, alwaysOpen = _b === void 0 ? false : _b, className = _a.className, flush = _a.flush, rest = __rest$1(_a, ["children", "activeItemKey", "alwaysOpen", "className", "flush"]);
    var _c = React$1.useState(activeItemKey), _activeItemKey = _c[0], setActiveKey = _c[1];
    return (React$1.createElement("div", __assign$1({ className: classNames$1('accordion', { 'accordion-flush': flush }, className) }, rest, { ref: ref }),
        React$1.createElement(CAccordionContext.Provider, { value: { _activeItemKey: _activeItemKey, alwaysOpen: alwaysOpen, setActiveKey: setActiveKey } }, children)));
});
CAccordion.propTypes = {
    alwaysOpen: PropTypes$1.bool,
    activeItemKey: PropTypes$1.oneOfType([PropTypes$1.number, PropTypes$1.string]),
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    flush: PropTypes$1.bool,
};
CAccordion.displayName = 'CAccordion';

var CAccordionItemContext = React$1.createContext({});
var CAccordionItem = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, itemKey = _a.itemKey, rest = __rest$1(_a, ["children", "className", "itemKey"]);
    var _itemKey = React$1.useRef(itemKey !== null && itemKey !== void 0 ? itemKey : Math.random().toString(36).slice(2, 11));
    var _b = React$1.useContext(CAccordionContext), _activeItemKey = _b._activeItemKey, alwaysOpen = _b.alwaysOpen, setActiveKey = _b.setActiveKey;
    var _c = React$1.useState(Boolean(_activeItemKey === _itemKey.current)), visible = _c[0], setVisible = _c[1];
    React$1.useEffect(function () {
        !alwaysOpen && visible && setActiveKey(_itemKey.current);
    }, [visible]);
    React$1.useEffect(function () {
        setVisible(Boolean(_activeItemKey === _itemKey.current));
    }, [_activeItemKey]);
    return (React$1.createElement("div", __assign$1({ className: classNames$1('accordion-item', className) }, rest, { ref: ref }),
        React$1.createElement(CAccordionItemContext.Provider, { value: { setVisible: setVisible, visible: visible } }, children)));
});
CAccordionItem.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    itemKey: PropTypes$1.oneOfType([PropTypes$1.number, PropTypes$1.string]),
};
CAccordionItem.displayName = 'CAccordionItem';

function _extends$1() {
  _extends$1 = Object.assign ? Object.assign.bind() : function (target) {
    for (var i = 1; i < arguments.length; i++) {
      var source = arguments[i];
      for (var key in source) {
        if (Object.prototype.hasOwnProperty.call(source, key)) {
          target[key] = source[key];
        }
      }
    }
    return target;
  };
  return _extends$1.apply(this, arguments);
}

function _objectWithoutPropertiesLoose$1(source, excluded) {
  if (source == null) return {};
  var target = {};
  var sourceKeys = Object.keys(source);
  var key, i;
  for (i = 0; i < sourceKeys.length; i++) {
    key = sourceKeys[i];
    if (excluded.indexOf(key) >= 0) continue;
    target[key] = source[key];
  }
  return target;
}

function _setPrototypeOf$1(o, p) {
  _setPrototypeOf$1 = Object.setPrototypeOf ? Object.setPrototypeOf.bind() : function _setPrototypeOf(o, p) {
    o.__proto__ = p;
    return o;
  };
  return _setPrototypeOf$1(o, p);
}

function _inheritsLoose(subClass, superClass) {
  subClass.prototype = Object.create(superClass.prototype);
  subClass.prototype.constructor = subClass;
  _setPrototypeOf$1(subClass, superClass);
}

/**
 * Checks if a given element has a CSS class.
 * 
 * @param element the element
 * @param className the CSS class name
 */
function hasClass(element, className) {
  if (element.classList) return !!className && element.classList.contains(className);
  return (" " + (element.className.baseVal || element.className) + " ").indexOf(" " + className + " ") !== -1;
}

/**
 * Adds a CSS class to a given element.
 * 
 * @param element the element
 * @param className the CSS class name
 */

function addClass(element, className) {
  if (element.classList) element.classList.add(className);else if (!hasClass(element, className)) if (typeof element.className === 'string') element.className = element.className + " " + className;else element.setAttribute('class', (element.className && element.className.baseVal || '') + " " + className);
}

function replaceClassName(origClass, classToRemove) {
  return origClass.replace(new RegExp("(^|\\s)" + classToRemove + "(?:\\s|$)", 'g'), '$1').replace(/\s+/g, ' ').replace(/^\s*|\s*$/g, '');
}
/**
 * Removes a CSS class from a given element.
 * 
 * @param element the element
 * @param className the CSS class name
 */


function removeClass$1(element, className) {
  if (element.classList) {
    element.classList.remove(className);
  } else if (typeof element.className === 'string') {
    element.className = replaceClassName(element.className, className);
  } else {
    element.setAttribute('class', replaceClassName(element.className && element.className.baseVal || '', className));
  }
}

var config = {
  disabled: false
};

var timeoutsShape = process.env.NODE_ENV !== 'production' ? PropTypes$1.oneOfType([PropTypes$1.number, PropTypes$1.shape({
  enter: PropTypes$1.number,
  exit: PropTypes$1.number,
  appear: PropTypes$1.number
}).isRequired]) : null;
var classNamesShape = process.env.NODE_ENV !== 'production' ? PropTypes$1.oneOfType([PropTypes$1.string, PropTypes$1.shape({
  enter: PropTypes$1.string,
  exit: PropTypes$1.string,
  active: PropTypes$1.string
}), PropTypes$1.shape({
  enter: PropTypes$1.string,
  enterDone: PropTypes$1.string,
  enterActive: PropTypes$1.string,
  exit: PropTypes$1.string,
  exitDone: PropTypes$1.string,
  exitActive: PropTypes$1.string
})]) : null;

var TransitionGroupContext = React$1.createContext(null);

var forceReflow = function forceReflow(node) {
  return node.scrollTop;
};

var UNMOUNTED = 'unmounted';
var EXITED = 'exited';
var ENTERING = 'entering';
var ENTERED = 'entered';
var EXITING = 'exiting';
/**
 * The Transition component lets you describe a transition from one component
 * state to another _over time_ with a simple declarative API. Most commonly
 * it's used to animate the mounting and unmounting of a component, but can also
 * be used to describe in-place transition states as well.
 *
 * ---
 *
 * **Note**: `Transition` is a platform-agnostic base component. If you're using
 * transitions in CSS, you'll probably want to use
 * [`CSSTransition`](https://reactcommunity.org/react-transition-group/css-transition)
 * instead. It inherits all the features of `Transition`, but contains
 * additional features necessary to play nice with CSS transitions (hence the
 * name of the component).
 *
 * ---
 *
 * By default the `Transition` component does not alter the behavior of the
 * component it renders, it only tracks "enter" and "exit" states for the
 * components. It's up to you to give meaning and effect to those states. For
 * example we can add styles to a component when it enters or exits:
 *
 * ```jsx
 * import { Transition } from 'react-transition-group';
 *
 * const duration = 300;
 *
 * const defaultStyle = {
 *   transition: `opacity ${duration}ms ease-in-out`,
 *   opacity: 0,
 * }
 *
 * const transitionStyles = {
 *   entering: { opacity: 1 },
 *   entered:  { opacity: 1 },
 *   exiting:  { opacity: 0 },
 *   exited:  { opacity: 0 },
 * };
 *
 * const Fade = ({ in: inProp }) => (
 *   <Transition in={inProp} timeout={duration}>
 *     {state => (
 *       <div style={{
 *         ...defaultStyle,
 *         ...transitionStyles[state]
 *       }}>
 *         I'm a fade Transition!
 *       </div>
 *     )}
 *   </Transition>
 * );
 * ```
 *
 * There are 4 main states a Transition can be in:
 *  - `'entering'`
 *  - `'entered'`
 *  - `'exiting'`
 *  - `'exited'`
 *
 * Transition state is toggled via the `in` prop. When `true` the component
 * begins the "Enter" stage. During this stage, the component will shift from
 * its current transition state, to `'entering'` for the duration of the
 * transition and then to the `'entered'` stage once it's complete. Let's take
 * the following example (we'll use the
 * [useState](https://reactjs.org/docs/hooks-reference.html#usestate) hook):
 *
 * ```jsx
 * function App() {
 *   const [inProp, setInProp] = useState(false);
 *   return (
 *     <div>
 *       <Transition in={inProp} timeout={500}>
 *         {state => (
 *           // ...
 *         )}
 *       </Transition>
 *       <button onClick={() => setInProp(true)}>
 *         Click to Enter
 *       </button>
 *     </div>
 *   );
 * }
 * ```
 *
 * When the button is clicked the component will shift to the `'entering'` state
 * and stay there for 500ms (the value of `timeout`) before it finally switches
 * to `'entered'`.
 *
 * When `in` is `false` the same thing happens except the state moves from
 * `'exiting'` to `'exited'`.
 */

var Transition = /*#__PURE__*/function (_React$Component) {
  _inheritsLoose(Transition, _React$Component);

  function Transition(props, context) {
    var _this;

    _this = _React$Component.call(this, props, context) || this;
    var parentGroup = context; // In the context of a TransitionGroup all enters are really appears

    var appear = parentGroup && !parentGroup.isMounting ? props.enter : props.appear;
    var initialStatus;
    _this.appearStatus = null;

    if (props.in) {
      if (appear) {
        initialStatus = EXITED;
        _this.appearStatus = ENTERING;
      } else {
        initialStatus = ENTERED;
      }
    } else {
      if (props.unmountOnExit || props.mountOnEnter) {
        initialStatus = UNMOUNTED;
      } else {
        initialStatus = EXITED;
      }
    }

    _this.state = {
      status: initialStatus
    };
    _this.nextCallback = null;
    return _this;
  }

  Transition.getDerivedStateFromProps = function getDerivedStateFromProps(_ref, prevState) {
    var nextIn = _ref.in;

    if (nextIn && prevState.status === UNMOUNTED) {
      return {
        status: EXITED
      };
    }

    return null;
  } // getSnapshotBeforeUpdate(prevProps) {
  //   let nextStatus = null
  //   if (prevProps !== this.props) {
  //     const { status } = this.state
  //     if (this.props.in) {
  //       if (status !== ENTERING && status !== ENTERED) {
  //         nextStatus = ENTERING
  //       }
  //     } else {
  //       if (status === ENTERING || status === ENTERED) {
  //         nextStatus = EXITING
  //       }
  //     }
  //   }
  //   return { nextStatus }
  // }
  ;

  var _proto = Transition.prototype;

  _proto.componentDidMount = function componentDidMount() {
    this.updateStatus(true, this.appearStatus);
  };

  _proto.componentDidUpdate = function componentDidUpdate(prevProps) {
    var nextStatus = null;

    if (prevProps !== this.props) {
      var status = this.state.status;

      if (this.props.in) {
        if (status !== ENTERING && status !== ENTERED) {
          nextStatus = ENTERING;
        }
      } else {
        if (status === ENTERING || status === ENTERED) {
          nextStatus = EXITING;
        }
      }
    }

    this.updateStatus(false, nextStatus);
  };

  _proto.componentWillUnmount = function componentWillUnmount() {
    this.cancelNextCallback();
  };

  _proto.getTimeouts = function getTimeouts() {
    var timeout = this.props.timeout;
    var exit, enter, appear;
    exit = enter = appear = timeout;

    if (timeout != null && typeof timeout !== 'number') {
      exit = timeout.exit;
      enter = timeout.enter; // TODO: remove fallback for next major

      appear = timeout.appear !== undefined ? timeout.appear : enter;
    }

    return {
      exit: exit,
      enter: enter,
      appear: appear
    };
  };

  _proto.updateStatus = function updateStatus(mounting, nextStatus) {
    if (mounting === void 0) {
      mounting = false;
    }

    if (nextStatus !== null) {
      // nextStatus will always be ENTERING or EXITING.
      this.cancelNextCallback();

      if (nextStatus === ENTERING) {
        if (this.props.unmountOnExit || this.props.mountOnEnter) {
          var node = this.props.nodeRef ? this.props.nodeRef.current : ReactDOM.findDOMNode(this); // https://github.com/reactjs/react-transition-group/pull/749
          // With unmountOnExit or mountOnEnter, the enter animation should happen at the transition between `exited` and `entering`.
          // To make the animation happen,  we have to separate each rendering and avoid being processed as batched.

          if (node) forceReflow(node);
        }

        this.performEnter(mounting);
      } else {
        this.performExit();
      }
    } else if (this.props.unmountOnExit && this.state.status === EXITED) {
      this.setState({
        status: UNMOUNTED
      });
    }
  };

  _proto.performEnter = function performEnter(mounting) {
    var _this2 = this;

    var enter = this.props.enter;
    var appearing = this.context ? this.context.isMounting : mounting;

    var _ref2 = this.props.nodeRef ? [appearing] : [ReactDOM.findDOMNode(this), appearing],
        maybeNode = _ref2[0],
        maybeAppearing = _ref2[1];

    var timeouts = this.getTimeouts();
    var enterTimeout = appearing ? timeouts.appear : timeouts.enter; // no enter animation skip right to ENTERED
    // if we are mounting and running this it means appear _must_ be set

    if (!mounting && !enter || config.disabled) {
      this.safeSetState({
        status: ENTERED
      }, function () {
        _this2.props.onEntered(maybeNode);
      });
      return;
    }

    this.props.onEnter(maybeNode, maybeAppearing);
    this.safeSetState({
      status: ENTERING
    }, function () {
      _this2.props.onEntering(maybeNode, maybeAppearing);

      _this2.onTransitionEnd(enterTimeout, function () {
        _this2.safeSetState({
          status: ENTERED
        }, function () {
          _this2.props.onEntered(maybeNode, maybeAppearing);
        });
      });
    });
  };

  _proto.performExit = function performExit() {
    var _this3 = this;

    var exit = this.props.exit;
    var timeouts = this.getTimeouts();
    var maybeNode = this.props.nodeRef ? undefined : ReactDOM.findDOMNode(this); // no exit animation skip right to EXITED

    if (!exit || config.disabled) {
      this.safeSetState({
        status: EXITED
      }, function () {
        _this3.props.onExited(maybeNode);
      });
      return;
    }

    this.props.onExit(maybeNode);
    this.safeSetState({
      status: EXITING
    }, function () {
      _this3.props.onExiting(maybeNode);

      _this3.onTransitionEnd(timeouts.exit, function () {
        _this3.safeSetState({
          status: EXITED
        }, function () {
          _this3.props.onExited(maybeNode);
        });
      });
    });
  };

  _proto.cancelNextCallback = function cancelNextCallback() {
    if (this.nextCallback !== null) {
      this.nextCallback.cancel();
      this.nextCallback = null;
    }
  };

  _proto.safeSetState = function safeSetState(nextState, callback) {
    // This shouldn't be necessary, but there are weird race conditions with
    // setState callbacks and unmounting in testing, so always make sure that
    // we can cancel any pending setState callbacks after we unmount.
    callback = this.setNextCallback(callback);
    this.setState(nextState, callback);
  };

  _proto.setNextCallback = function setNextCallback(callback) {
    var _this4 = this;

    var active = true;

    this.nextCallback = function (event) {
      if (active) {
        active = false;
        _this4.nextCallback = null;
        callback(event);
      }
    };

    this.nextCallback.cancel = function () {
      active = false;
    };

    return this.nextCallback;
  };

  _proto.onTransitionEnd = function onTransitionEnd(timeout, handler) {
    this.setNextCallback(handler);
    var node = this.props.nodeRef ? this.props.nodeRef.current : ReactDOM.findDOMNode(this);
    var doesNotHaveTimeoutOrListener = timeout == null && !this.props.addEndListener;

    if (!node || doesNotHaveTimeoutOrListener) {
      setTimeout(this.nextCallback, 0);
      return;
    }

    if (this.props.addEndListener) {
      var _ref3 = this.props.nodeRef ? [this.nextCallback] : [node, this.nextCallback],
          maybeNode = _ref3[0],
          maybeNextCallback = _ref3[1];

      this.props.addEndListener(maybeNode, maybeNextCallback);
    }

    if (timeout != null) {
      setTimeout(this.nextCallback, timeout);
    }
  };

  _proto.render = function render() {
    var status = this.state.status;

    if (status === UNMOUNTED) {
      return null;
    }

    var _this$props = this.props,
        children = _this$props.children;
        _this$props.in;
        _this$props.mountOnEnter;
        _this$props.unmountOnExit;
        _this$props.appear;
        _this$props.enter;
        _this$props.exit;
        _this$props.timeout;
        _this$props.addEndListener;
        _this$props.onEnter;
        _this$props.onEntering;
        _this$props.onEntered;
        _this$props.onExit;
        _this$props.onExiting;
        _this$props.onExited;
        _this$props.nodeRef;
        var childProps = _objectWithoutPropertiesLoose$1(_this$props, ["children", "in", "mountOnEnter", "unmountOnExit", "appear", "enter", "exit", "timeout", "addEndListener", "onEnter", "onEntering", "onEntered", "onExit", "onExiting", "onExited", "nodeRef"]);

    return (
      /*#__PURE__*/
      // allows for nested Transitions
      React$1.createElement(TransitionGroupContext.Provider, {
        value: null
      }, typeof children === 'function' ? children(status, childProps) : React$1.cloneElement(React$1.Children.only(children), childProps))
    );
  };

  return Transition;
}(React$1.Component);

Transition.contextType = TransitionGroupContext;
Transition.propTypes = process.env.NODE_ENV !== "production" ? {
  /**
   * A React reference to DOM element that need to transition:
   * https://stackoverflow.com/a/51127130/4671932
   *
   *   - When `nodeRef` prop is used, `node` is not passed to callback functions
   *      (e.g. `onEnter`) because user already has direct access to the node.
   *   - When changing `key` prop of `Transition` in a `TransitionGroup` a new
   *     `nodeRef` need to be provided to `Transition` with changed `key` prop
   *     (see
   *     [test/CSSTransition-test.js](https://github.com/reactjs/react-transition-group/blob/13435f897b3ab71f6e19d724f145596f5910581c/test/CSSTransition-test.js#L362-L437)).
   */
  nodeRef: PropTypes$1.shape({
    current: typeof Element === 'undefined' ? PropTypes$1.any : function (propValue, key, componentName, location, propFullName, secret) {
      var value = propValue[key];
      return PropTypes$1.instanceOf(value && 'ownerDocument' in value ? value.ownerDocument.defaultView.Element : Element)(propValue, key, componentName, location, propFullName, secret);
    }
  }),

  /**
   * A `function` child can be used instead of a React element. This function is
   * called with the current transition status (`'entering'`, `'entered'`,
   * `'exiting'`, `'exited'`), which can be used to apply context
   * specific props to a component.
   *
   * ```jsx
   * <Transition in={this.state.in} timeout={150}>
   *   {state => (
   *     <MyComponent className={`fade fade-${state}`} />
   *   )}
   * </Transition>
   * ```
   */
  children: PropTypes$1.oneOfType([PropTypes$1.func.isRequired, PropTypes$1.element.isRequired]).isRequired,

  /**
   * Show the component; triggers the enter or exit states
   */
  in: PropTypes$1.bool,

  /**
   * By default the child component is mounted immediately along with
   * the parent `Transition` component. If you want to "lazy mount" the component on the
   * first `in={true}` you can set `mountOnEnter`. After the first enter transition the component will stay
   * mounted, even on "exited", unless you also specify `unmountOnExit`.
   */
  mountOnEnter: PropTypes$1.bool,

  /**
   * By default the child component stays mounted after it reaches the `'exited'` state.
   * Set `unmountOnExit` if you'd prefer to unmount the component after it finishes exiting.
   */
  unmountOnExit: PropTypes$1.bool,

  /**
   * By default the child component does not perform the enter transition when
   * it first mounts, regardless of the value of `in`. If you want this
   * behavior, set both `appear` and `in` to `true`.
   *
   * > **Note**: there are no special appear states like `appearing`/`appeared`, this prop
   * > only adds an additional enter transition. However, in the
   * > `<CSSTransition>` component that first enter transition does result in
   * > additional `.appear-*` classes, that way you can choose to style it
   * > differently.
   */
  appear: PropTypes$1.bool,

  /**
   * Enable or disable enter transitions.
   */
  enter: PropTypes$1.bool,

  /**
   * Enable or disable exit transitions.
   */
  exit: PropTypes$1.bool,

  /**
   * The duration of the transition, in milliseconds.
   * Required unless `addEndListener` is provided.
   *
   * You may specify a single timeout for all transitions:
   *
   * ```jsx
   * timeout={500}
   * ```
   *
   * or individually:
   *
   * ```jsx
   * timeout={{
   *  appear: 500,
   *  enter: 300,
   *  exit: 500,
   * }}
   * ```
   *
   * - `appear` defaults to the value of `enter`
   * - `enter` defaults to `0`
   * - `exit` defaults to `0`
   *
   * @type {number | { enter?: number, exit?: number, appear?: number }}
   */
  timeout: function timeout(props) {
    var pt = timeoutsShape;
    if (!props.addEndListener) pt = pt.isRequired;

    for (var _len = arguments.length, args = new Array(_len > 1 ? _len - 1 : 0), _key = 1; _key < _len; _key++) {
      args[_key - 1] = arguments[_key];
    }

    return pt.apply(void 0, [props].concat(args));
  },

  /**
   * Add a custom transition end trigger. Called with the transitioning
   * DOM node and a `done` callback. Allows for more fine grained transition end
   * logic. Timeouts are still used as a fallback if provided.
   *
   * **Note**: when `nodeRef` prop is passed, `node` is not passed.
   *
   * ```jsx
   * addEndListener={(node, done) => {
   *   // use the css transitionend event to mark the finish of a transition
   *   node.addEventListener('transitionend', done, false);
   * }}
   * ```
   */
  addEndListener: PropTypes$1.func,

  /**
   * Callback fired before the "entering" status is applied. An extra parameter
   * `isAppearing` is supplied to indicate if the enter stage is occurring on the initial mount
   *
   * **Note**: when `nodeRef` prop is passed, `node` is not passed.
   *
   * @type Function(node: HtmlElement, isAppearing: bool) -> void
   */
  onEnter: PropTypes$1.func,

  /**
   * Callback fired after the "entering" status is applied. An extra parameter
   * `isAppearing` is supplied to indicate if the enter stage is occurring on the initial mount
   *
   * **Note**: when `nodeRef` prop is passed, `node` is not passed.
   *
   * @type Function(node: HtmlElement, isAppearing: bool)
   */
  onEntering: PropTypes$1.func,

  /**
   * Callback fired after the "entered" status is applied. An extra parameter
   * `isAppearing` is supplied to indicate if the enter stage is occurring on the initial mount
   *
   * **Note**: when `nodeRef` prop is passed, `node` is not passed.
   *
   * @type Function(node: HtmlElement, isAppearing: bool) -> void
   */
  onEntered: PropTypes$1.func,

  /**
   * Callback fired before the "exiting" status is applied.
   *
   * **Note**: when `nodeRef` prop is passed, `node` is not passed.
   *
   * @type Function(node: HtmlElement) -> void
   */
  onExit: PropTypes$1.func,

  /**
   * Callback fired after the "exiting" status is applied.
   *
   * **Note**: when `nodeRef` prop is passed, `node` is not passed.
   *
   * @type Function(node: HtmlElement) -> void
   */
  onExiting: PropTypes$1.func,

  /**
   * Callback fired after the "exited" status is applied.
   *
   * **Note**: when `nodeRef` prop is passed, `node` is not passed
   *
   * @type Function(node: HtmlElement) -> void
   */
  onExited: PropTypes$1.func
} : {}; // Name the function so it is clearer in the documentation

function noop() {}

Transition.defaultProps = {
  in: false,
  mountOnEnter: false,
  unmountOnExit: false,
  appear: false,
  enter: true,
  exit: true,
  onEnter: noop,
  onEntering: noop,
  onEntered: noop,
  onExit: noop,
  onExiting: noop,
  onExited: noop
};
Transition.UNMOUNTED = UNMOUNTED;
Transition.EXITED = EXITED;
Transition.ENTERING = ENTERING;
Transition.ENTERED = ENTERED;
Transition.EXITING = EXITING;
var Transition$1 = Transition;

var _addClass = function addClass$1(node, classes) {
  return node && classes && classes.split(' ').forEach(function (c) {
    return addClass(node, c);
  });
};

var removeClass = function removeClass(node, classes) {
  return node && classes && classes.split(' ').forEach(function (c) {
    return removeClass$1(node, c);
  });
};
/**
 * A transition component inspired by the excellent
 * [ng-animate](https://docs.angularjs.org/api/ngAnimate) library, you should
 * use it if you're using CSS transitions or animations. It's built upon the
 * [`Transition`](https://reactcommunity.org/react-transition-group/transition)
 * component, so it inherits all of its props.
 *
 * `CSSTransition` applies a pair of class names during the `appear`, `enter`,
 * and `exit` states of the transition. The first class is applied and then a
 * second `*-active` class in order to activate the CSS transition. After the
 * transition, matching `*-done` class names are applied to persist the
 * transition state.
 *
 * ```jsx
 * function App() {
 *   const [inProp, setInProp] = useState(false);
 *   return (
 *     <div>
 *       <CSSTransition in={inProp} timeout={200} classNames="my-node">
 *         <div>
 *           {"I'll receive my-node-* classes"}
 *         </div>
 *       </CSSTransition>
 *       <button type="button" onClick={() => setInProp(true)}>
 *         Click to Enter
 *       </button>
 *     </div>
 *   );
 * }
 * ```
 *
 * When the `in` prop is set to `true`, the child component will first receive
 * the class `example-enter`, then the `example-enter-active` will be added in
 * the next tick. `CSSTransition` [forces a
 * reflow](https://github.com/reactjs/react-transition-group/blob/5007303e729a74be66a21c3e2205e4916821524b/src/CSSTransition.js#L208-L215)
 * between before adding the `example-enter-active`. This is an important trick
 * because it allows us to transition between `example-enter` and
 * `example-enter-active` even though they were added immediately one after
 * another. Most notably, this is what makes it possible for us to animate
 * _appearance_.
 *
 * ```css
 * .my-node-enter {
 *   opacity: 0;
 * }
 * .my-node-enter-active {
 *   opacity: 1;
 *   transition: opacity 200ms;
 * }
 * .my-node-exit {
 *   opacity: 1;
 * }
 * .my-node-exit-active {
 *   opacity: 0;
 *   transition: opacity 200ms;
 * }
 * ```
 *
 * `*-active` classes represent which styles you want to animate **to**, so it's
 * important to add `transition` declaration only to them, otherwise transitions
 * might not behave as intended! This might not be obvious when the transitions
 * are symmetrical, i.e. when `*-enter-active` is the same as `*-exit`, like in
 * the example above (minus `transition`), but it becomes apparent in more
 * complex transitions.
 *
 * **Note**: If you're using the
 * [`appear`](http://reactcommunity.org/react-transition-group/transition#Transition-prop-appear)
 * prop, make sure to define styles for `.appear-*` classes as well.
 */


var CSSTransition = /*#__PURE__*/function (_React$Component) {
  _inheritsLoose(CSSTransition, _React$Component);

  function CSSTransition() {
    var _this;

    for (var _len = arguments.length, args = new Array(_len), _key = 0; _key < _len; _key++) {
      args[_key] = arguments[_key];
    }

    _this = _React$Component.call.apply(_React$Component, [this].concat(args)) || this;
    _this.appliedClasses = {
      appear: {},
      enter: {},
      exit: {}
    };

    _this.onEnter = function (maybeNode, maybeAppearing) {
      var _this$resolveArgument = _this.resolveArguments(maybeNode, maybeAppearing),
          node = _this$resolveArgument[0],
          appearing = _this$resolveArgument[1];

      _this.removeClasses(node, 'exit');

      _this.addClass(node, appearing ? 'appear' : 'enter', 'base');

      if (_this.props.onEnter) {
        _this.props.onEnter(maybeNode, maybeAppearing);
      }
    };

    _this.onEntering = function (maybeNode, maybeAppearing) {
      var _this$resolveArgument2 = _this.resolveArguments(maybeNode, maybeAppearing),
          node = _this$resolveArgument2[0],
          appearing = _this$resolveArgument2[1];

      var type = appearing ? 'appear' : 'enter';

      _this.addClass(node, type, 'active');

      if (_this.props.onEntering) {
        _this.props.onEntering(maybeNode, maybeAppearing);
      }
    };

    _this.onEntered = function (maybeNode, maybeAppearing) {
      var _this$resolveArgument3 = _this.resolveArguments(maybeNode, maybeAppearing),
          node = _this$resolveArgument3[0],
          appearing = _this$resolveArgument3[1];

      var type = appearing ? 'appear' : 'enter';

      _this.removeClasses(node, type);

      _this.addClass(node, type, 'done');

      if (_this.props.onEntered) {
        _this.props.onEntered(maybeNode, maybeAppearing);
      }
    };

    _this.onExit = function (maybeNode) {
      var _this$resolveArgument4 = _this.resolveArguments(maybeNode),
          node = _this$resolveArgument4[0];

      _this.removeClasses(node, 'appear');

      _this.removeClasses(node, 'enter');

      _this.addClass(node, 'exit', 'base');

      if (_this.props.onExit) {
        _this.props.onExit(maybeNode);
      }
    };

    _this.onExiting = function (maybeNode) {
      var _this$resolveArgument5 = _this.resolveArguments(maybeNode),
          node = _this$resolveArgument5[0];

      _this.addClass(node, 'exit', 'active');

      if (_this.props.onExiting) {
        _this.props.onExiting(maybeNode);
      }
    };

    _this.onExited = function (maybeNode) {
      var _this$resolveArgument6 = _this.resolveArguments(maybeNode),
          node = _this$resolveArgument6[0];

      _this.removeClasses(node, 'exit');

      _this.addClass(node, 'exit', 'done');

      if (_this.props.onExited) {
        _this.props.onExited(maybeNode);
      }
    };

    _this.resolveArguments = function (maybeNode, maybeAppearing) {
      return _this.props.nodeRef ? [_this.props.nodeRef.current, maybeNode] // here `maybeNode` is actually `appearing`
      : [maybeNode, maybeAppearing];
    };

    _this.getClassNames = function (type) {
      var classNames = _this.props.classNames;
      var isStringClassNames = typeof classNames === 'string';
      var prefix = isStringClassNames && classNames ? classNames + "-" : '';
      var baseClassName = isStringClassNames ? "" + prefix + type : classNames[type];
      var activeClassName = isStringClassNames ? baseClassName + "-active" : classNames[type + "Active"];
      var doneClassName = isStringClassNames ? baseClassName + "-done" : classNames[type + "Done"];
      return {
        baseClassName: baseClassName,
        activeClassName: activeClassName,
        doneClassName: doneClassName
      };
    };

    return _this;
  }

  var _proto = CSSTransition.prototype;

  _proto.addClass = function addClass(node, type, phase) {
    var className = this.getClassNames(type)[phase + "ClassName"];

    var _this$getClassNames = this.getClassNames('enter'),
        doneClassName = _this$getClassNames.doneClassName;

    if (type === 'appear' && phase === 'done' && doneClassName) {
      className += " " + doneClassName;
    } // This is to force a repaint,
    // which is necessary in order to transition styles when adding a class name.


    if (phase === 'active') {
      if (node) forceReflow(node);
    }

    if (className) {
      this.appliedClasses[type][phase] = className;

      _addClass(node, className);
    }
  };

  _proto.removeClasses = function removeClasses(node, type) {
    var _this$appliedClasses$ = this.appliedClasses[type],
        baseClassName = _this$appliedClasses$.base,
        activeClassName = _this$appliedClasses$.active,
        doneClassName = _this$appliedClasses$.done;
    this.appliedClasses[type] = {};

    if (baseClassName) {
      removeClass(node, baseClassName);
    }

    if (activeClassName) {
      removeClass(node, activeClassName);
    }

    if (doneClassName) {
      removeClass(node, doneClassName);
    }
  };

  _proto.render = function render() {
    var _this$props = this.props;
        _this$props.classNames;
        var props = _objectWithoutPropertiesLoose$1(_this$props, ["classNames"]);

    return /*#__PURE__*/React$1.createElement(Transition$1, _extends$1({}, props, {
      onEnter: this.onEnter,
      onEntered: this.onEntered,
      onEntering: this.onEntering,
      onExit: this.onExit,
      onExiting: this.onExiting,
      onExited: this.onExited
    }));
  };

  return CSSTransition;
}(React$1.Component);

CSSTransition.defaultProps = {
  classNames: ''
};
CSSTransition.propTypes = process.env.NODE_ENV !== "production" ? _extends$1({}, Transition$1.propTypes, {
  /**
   * The animation classNames applied to the component as it appears, enters,
   * exits or has finished the transition. A single name can be provided, which
   * will be suffixed for each stage, e.g. `classNames="fade"` applies:
   *
   * - `fade-appear`, `fade-appear-active`, `fade-appear-done`
   * - `fade-enter`, `fade-enter-active`, `fade-enter-done`
   * - `fade-exit`, `fade-exit-active`, `fade-exit-done`
   *
   * A few details to note about how these classes are applied:
   *
   * 1. They are _joined_ with the ones that are already defined on the child
   *    component, so if you want to add some base styles, you can use
   *    `className` without worrying that it will be overridden.
   *
   * 2. If the transition component mounts with `in={false}`, no classes are
   *    applied yet. You might be expecting `*-exit-done`, but if you think
   *    about it, a component cannot finish exiting if it hasn't entered yet.
   *
   * 2. `fade-appear-done` and `fade-enter-done` will _both_ be applied. This
   *    allows you to define different behavior for when appearing is done and
   *    when regular entering is done, using selectors like
   *    `.fade-enter-done:not(.fade-appear-done)`. For example, you could apply
   *    an epic entrance animation when element first appears in the DOM using
   *    [Animate.css](https://daneden.github.io/animate.css/). Otherwise you can
   *    simply use `fade-enter-done` for defining both cases.
   *
   * Each individual classNames can also be specified independently like:
   *
   * ```js
   * classNames={{
   *  appear: 'my-appear',
   *  appearActive: 'my-active-appear',
   *  appearDone: 'my-done-appear',
   *  enter: 'my-enter',
   *  enterActive: 'my-active-enter',
   *  enterDone: 'my-done-enter',
   *  exit: 'my-exit',
   *  exitActive: 'my-active-exit',
   *  exitDone: 'my-done-exit',
   * }}
   * ```
   *
   * If you want to set these classes using CSS Modules:
   *
   * ```js
   * import styles from './styles.css';
   * ```
   *
   * you might want to use camelCase in your CSS file, that way could simply
   * spread them instead of listing them one by one:
   *
   * ```js
   * classNames={{ ...styles }}
   * ```
   *
   * @type {string | {
   *  appear?: string,
   *  appearActive?: string,
   *  appearDone?: string,
   *  enter?: string,
   *  enterActive?: string,
   *  enterDone?: string,
   *  exit?: string,
   *  exitActive?: string,
   *  exitDone?: string,
   * }}
   */
  classNames: classNamesShape,

  /**
   * A `<Transition>` callback fired immediately after the 'enter' or 'appear' class is
   * applied.
   *
   * **Note**: when `nodeRef` prop is passed, `node` is not passed.
   *
   * @type Function(node: HtmlElement, isAppearing: bool)
   */
  onEnter: PropTypes$1.func,

  /**
   * A `<Transition>` callback fired immediately after the 'enter-active' or
   * 'appear-active' class is applied.
   *
   * **Note**: when `nodeRef` prop is passed, `node` is not passed.
   *
   * @type Function(node: HtmlElement, isAppearing: bool)
   */
  onEntering: PropTypes$1.func,

  /**
   * A `<Transition>` callback fired immediately after the 'enter' or
   * 'appear' classes are **removed** and the `done` class is added to the DOM node.
   *
   * **Note**: when `nodeRef` prop is passed, `node` is not passed.
   *
   * @type Function(node: HtmlElement, isAppearing: bool)
   */
  onEntered: PropTypes$1.func,

  /**
   * A `<Transition>` callback fired immediately after the 'exit' class is
   * applied.
   *
   * **Note**: when `nodeRef` prop is passed, `node` is not passed
   *
   * @type Function(node: HtmlElement)
   */
  onExit: PropTypes$1.func,

  /**
   * A `<Transition>` callback fired immediately after the 'exit-active' is applied.
   *
   * **Note**: when `nodeRef` prop is passed, `node` is not passed
   *
   * @type Function(node: HtmlElement)
   */
  onExiting: PropTypes$1.func,

  /**
   * A `<Transition>` callback fired immediately after the 'exit' classes
   * are **removed** and the `exit-done` class is added to the DOM node.
   *
   * **Note**: when `nodeRef` prop is passed, `node` is not passed
   *
   * @type Function(node: HtmlElement)
   */
  onExited: PropTypes$1.func
}) : {};
var CSSTransition$1 = CSSTransition;

var useDebouncedCallback = function (callback, delay) {
    var timeout = React$1.useRef();
    return React$1.useCallback(function () {
        var args = [];
        for (var _i = 0; _i < arguments.length; _i++) {
            args[_i] = arguments[_i];
        }
        var handler = function () {
            clearTimeout(timeout.current);
            callback.apply(void 0, args);
        };
        clearTimeout(timeout.current);
        timeout.current = setTimeout(handler, delay);
    }, [callback, delay]);
};

// code borrowed from https://github.com/reach/reach-ui
// problem described https://github.com/facebook/react/issues/13029
// eslint-disable-next-line @typescript-eslint/no-explicit-any
function useForkedRef() {
    var refs = [];
    for (var _i = 0; _i < arguments.length; _i++) {
        refs[_i] = arguments[_i];
    }
    return React$1.useMemo(function () {
        if (refs.every(function (ref) { return ref == null; })) {
            return null;
        }
        // eslint-disable-next-line @typescript-eslint/no-explicit-any
        return function (node) {
            refs.forEach(function (ref) {
                assignRef(ref, node);
            });
        };
    }, refs);
}
// eslint-disable-next-line @typescript-eslint/no-explicit-any
function assignRef(ref, 
// eslint-disable-next-line @typescript-eslint/no-explicit-any
value) {
    if (ref == null)
        return;
    if (isFunction(ref)) {
        ref(value);
    }
    else {
        try {
            ref.current = value;
        }
        catch (_a) {
            throw new Error("Cannot assign value \"".concat(value, "\" to ref \"").concat(ref, "\""));
        }
    }
}
// eslint-disable-next-line @typescript-eslint/no-explicit-any, @typescript-eslint/ban-types
function isFunction(value) {
    return !!(value && {}.toString.call(value) == '[object Function]');
}

var useIsVisible = function (ref) {
    var _a = React$1.useState(false), isIntersecting = _a[0], setIntersecting = _a[1];
    React$1.useEffect(function () {
        var observer = new IntersectionObserver(function (_a) {
            var entry = _a[0];
            return setIntersecting(entry.isIntersecting);
        });
        ref.current && observer.observe(ref.current);
        return function () { return observer.disconnect(); };
    }, []);
    return isIntersecting;
};

var top = 'top';
var bottom = 'bottom';
var right = 'right';
var left = 'left';
var auto = 'auto';
var basePlacements = [top, bottom, right, left];
var start = 'start';
var end = 'end';
var clippingParents = 'clippingParents';
var viewport = 'viewport';
var popper = 'popper';
var reference = 'reference';
var variationPlacements = /*#__PURE__*/basePlacements.reduce(function (acc, placement) {
  return acc.concat([placement + "-" + start, placement + "-" + end]);
}, []);
var placements = /*#__PURE__*/[].concat(basePlacements, [auto]).reduce(function (acc, placement) {
  return acc.concat([placement, placement + "-" + start, placement + "-" + end]);
}, []); // modifiers that need to read the DOM

var beforeRead = 'beforeRead';
var read = 'read';
var afterRead = 'afterRead'; // pure-logic modifiers

var beforeMain = 'beforeMain';
var main = 'main';
var afterMain = 'afterMain'; // modifier with the purpose to write to the DOM (or write into a framework state)

var beforeWrite = 'beforeWrite';
var write = 'write';
var afterWrite = 'afterWrite';
var modifierPhases = [beforeRead, read, afterRead, beforeMain, main, afterMain, beforeWrite, write, afterWrite];

function getNodeName(element) {
  return element ? (element.nodeName || '').toLowerCase() : null;
}

function getWindow(node) {
  if (node == null) {
    return window;
  }

  if (node.toString() !== '[object Window]') {
    var ownerDocument = node.ownerDocument;
    return ownerDocument ? ownerDocument.defaultView || window : window;
  }

  return node;
}

function isElement(node) {
  var OwnElement = getWindow(node).Element;
  return node instanceof OwnElement || node instanceof Element;
}

function isHTMLElement(node) {
  var OwnElement = getWindow(node).HTMLElement;
  return node instanceof OwnElement || node instanceof HTMLElement;
}

function isShadowRoot(node) {
  // IE 11 has no ShadowRoot
  if (typeof ShadowRoot === 'undefined') {
    return false;
  }

  var OwnElement = getWindow(node).ShadowRoot;
  return node instanceof OwnElement || node instanceof ShadowRoot;
}

// and applies them to the HTMLElements such as popper and arrow

function applyStyles(_ref) {
  var state = _ref.state;
  Object.keys(state.elements).forEach(function (name) {
    var style = state.styles[name] || {};
    var attributes = state.attributes[name] || {};
    var element = state.elements[name]; // arrow is optional + virtual elements

    if (!isHTMLElement(element) || !getNodeName(element)) {
      return;
    } // Flow doesn't support to extend this property, but it's the most
    // effective way to apply styles to an HTMLElement
    // $FlowFixMe[cannot-write]


    Object.assign(element.style, style);
    Object.keys(attributes).forEach(function (name) {
      var value = attributes[name];

      if (value === false) {
        element.removeAttribute(name);
      } else {
        element.setAttribute(name, value === true ? '' : value);
      }
    });
  });
}

function effect$2(_ref2) {
  var state = _ref2.state;
  var initialStyles = {
    popper: {
      position: state.options.strategy,
      left: '0',
      top: '0',
      margin: '0'
    },
    arrow: {
      position: 'absolute'
    },
    reference: {}
  };
  Object.assign(state.elements.popper.style, initialStyles.popper);
  state.styles = initialStyles;

  if (state.elements.arrow) {
    Object.assign(state.elements.arrow.style, initialStyles.arrow);
  }

  return function () {
    Object.keys(state.elements).forEach(function (name) {
      var element = state.elements[name];
      var attributes = state.attributes[name] || {};
      var styleProperties = Object.keys(state.styles.hasOwnProperty(name) ? state.styles[name] : initialStyles[name]); // Set all values to an empty string to unset them

      var style = styleProperties.reduce(function (style, property) {
        style[property] = '';
        return style;
      }, {}); // arrow is optional + virtual elements

      if (!isHTMLElement(element) || !getNodeName(element)) {
        return;
      }

      Object.assign(element.style, style);
      Object.keys(attributes).forEach(function (attribute) {
        element.removeAttribute(attribute);
      });
    });
  };
} // eslint-disable-next-line import/no-unused-modules


var applyStyles$1 = {
  name: 'applyStyles',
  enabled: true,
  phase: 'write',
  fn: applyStyles,
  effect: effect$2,
  requires: ['computeStyles']
};

function getBasePlacement(placement) {
  return placement.split('-')[0];
}

var max = Math.max;
var min = Math.min;
var round = Math.round;

function getUAString() {
  var uaData = navigator.userAgentData;

  if (uaData != null && uaData.brands && Array.isArray(uaData.brands)) {
    return uaData.brands.map(function (item) {
      return item.brand + "/" + item.version;
    }).join(' ');
  }

  return navigator.userAgent;
}

function isLayoutViewport() {
  return !/^((?!chrome|android).)*safari/i.test(getUAString());
}

function getBoundingClientRect(element, includeScale, isFixedStrategy) {
  if (includeScale === void 0) {
    includeScale = false;
  }

  if (isFixedStrategy === void 0) {
    isFixedStrategy = false;
  }

  var clientRect = element.getBoundingClientRect();
  var scaleX = 1;
  var scaleY = 1;

  if (includeScale && isHTMLElement(element)) {
    scaleX = element.offsetWidth > 0 ? round(clientRect.width) / element.offsetWidth || 1 : 1;
    scaleY = element.offsetHeight > 0 ? round(clientRect.height) / element.offsetHeight || 1 : 1;
  }

  var _ref = isElement(element) ? getWindow(element) : window,
      visualViewport = _ref.visualViewport;

  var addVisualOffsets = !isLayoutViewport() && isFixedStrategy;
  var x = (clientRect.left + (addVisualOffsets && visualViewport ? visualViewport.offsetLeft : 0)) / scaleX;
  var y = (clientRect.top + (addVisualOffsets && visualViewport ? visualViewport.offsetTop : 0)) / scaleY;
  var width = clientRect.width / scaleX;
  var height = clientRect.height / scaleY;
  return {
    width: width,
    height: height,
    top: y,
    right: x + width,
    bottom: y + height,
    left: x,
    x: x,
    y: y
  };
}

// means it doesn't take into account transforms.

function getLayoutRect(element) {
  var clientRect = getBoundingClientRect(element); // Use the clientRect sizes if it's not been transformed.
  // Fixes https://github.com/popperjs/popper-core/issues/1223

  var width = element.offsetWidth;
  var height = element.offsetHeight;

  if (Math.abs(clientRect.width - width) <= 1) {
    width = clientRect.width;
  }

  if (Math.abs(clientRect.height - height) <= 1) {
    height = clientRect.height;
  }

  return {
    x: element.offsetLeft,
    y: element.offsetTop,
    width: width,
    height: height
  };
}

function contains(parent, child) {
  var rootNode = child.getRootNode && child.getRootNode(); // First, attempt with faster native method

  if (parent.contains(child)) {
    return true;
  } // then fallback to custom implementation with Shadow DOM support
  else if (rootNode && isShadowRoot(rootNode)) {
      var next = child;

      do {
        if (next && parent.isSameNode(next)) {
          return true;
        } // $FlowFixMe[prop-missing]: need a better way to handle this...


        next = next.parentNode || next.host;
      } while (next);
    } // Give up, the result is false


  return false;
}

function getComputedStyle$1(element) {
  return getWindow(element).getComputedStyle(element);
}

function isTableElement(element) {
  return ['table', 'td', 'th'].indexOf(getNodeName(element)) >= 0;
}

function getDocumentElement(element) {
  // $FlowFixMe[incompatible-return]: assume body is always available
  return ((isElement(element) ? element.ownerDocument : // $FlowFixMe[prop-missing]
  element.document) || window.document).documentElement;
}

function getParentNode(element) {
  if (getNodeName(element) === 'html') {
    return element;
  }

  return (// this is a quicker (but less type safe) way to save quite some bytes from the bundle
    // $FlowFixMe[incompatible-return]
    // $FlowFixMe[prop-missing]
    element.assignedSlot || // step into the shadow DOM of the parent of a slotted node
    element.parentNode || ( // DOM Element detected
    isShadowRoot(element) ? element.host : null) || // ShadowRoot detected
    // $FlowFixMe[incompatible-call]: HTMLElement is a Node
    getDocumentElement(element) // fallback

  );
}

function getTrueOffsetParent(element) {
  if (!isHTMLElement(element) || // https://github.com/popperjs/popper-core/issues/837
  getComputedStyle$1(element).position === 'fixed') {
    return null;
  }

  return element.offsetParent;
} // `.offsetParent` reports `null` for fixed elements, while absolute elements
// return the containing block


function getContainingBlock(element) {
  var isFirefox = /firefox/i.test(getUAString());
  var isIE = /Trident/i.test(getUAString());

  if (isIE && isHTMLElement(element)) {
    // In IE 9, 10 and 11 fixed elements containing block is always established by the viewport
    var elementCss = getComputedStyle$1(element);

    if (elementCss.position === 'fixed') {
      return null;
    }
  }

  var currentNode = getParentNode(element);

  if (isShadowRoot(currentNode)) {
    currentNode = currentNode.host;
  }

  while (isHTMLElement(currentNode) && ['html', 'body'].indexOf(getNodeName(currentNode)) < 0) {
    var css = getComputedStyle$1(currentNode); // This is non-exhaustive but covers the most common CSS properties that
    // create a containing block.
    // https://developer.mozilla.org/en-US/docs/Web/CSS/Containing_block#identifying_the_containing_block

    if (css.transform !== 'none' || css.perspective !== 'none' || css.contain === 'paint' || ['transform', 'perspective'].indexOf(css.willChange) !== -1 || isFirefox && css.willChange === 'filter' || isFirefox && css.filter && css.filter !== 'none') {
      return currentNode;
    } else {
      currentNode = currentNode.parentNode;
    }
  }

  return null;
} // Gets the closest ancestor positioned element. Handles some edge cases,
// such as table ancestors and cross browser bugs.


function getOffsetParent(element) {
  var window = getWindow(element);
  var offsetParent = getTrueOffsetParent(element);

  while (offsetParent && isTableElement(offsetParent) && getComputedStyle$1(offsetParent).position === 'static') {
    offsetParent = getTrueOffsetParent(offsetParent);
  }

  if (offsetParent && (getNodeName(offsetParent) === 'html' || getNodeName(offsetParent) === 'body' && getComputedStyle$1(offsetParent).position === 'static')) {
    return window;
  }

  return offsetParent || getContainingBlock(element) || window;
}

function getMainAxisFromPlacement(placement) {
  return ['top', 'bottom'].indexOf(placement) >= 0 ? 'x' : 'y';
}

function within(min$1, value, max$1) {
  return max(min$1, min(value, max$1));
}
function withinMaxClamp(min, value, max) {
  var v = within(min, value, max);
  return v > max ? max : v;
}

function getFreshSideObject() {
  return {
    top: 0,
    right: 0,
    bottom: 0,
    left: 0
  };
}

function mergePaddingObject(paddingObject) {
  return Object.assign({}, getFreshSideObject(), paddingObject);
}

function expandToHashMap(value, keys) {
  return keys.reduce(function (hashMap, key) {
    hashMap[key] = value;
    return hashMap;
  }, {});
}

var toPaddingObject = function toPaddingObject(padding, state) {
  padding = typeof padding === 'function' ? padding(Object.assign({}, state.rects, {
    placement: state.placement
  })) : padding;
  return mergePaddingObject(typeof padding !== 'number' ? padding : expandToHashMap(padding, basePlacements));
};

function arrow(_ref) {
  var _state$modifiersData$;

  var state = _ref.state,
      name = _ref.name,
      options = _ref.options;
  var arrowElement = state.elements.arrow;
  var popperOffsets = state.modifiersData.popperOffsets;
  var basePlacement = getBasePlacement(state.placement);
  var axis = getMainAxisFromPlacement(basePlacement);
  var isVertical = [left, right].indexOf(basePlacement) >= 0;
  var len = isVertical ? 'height' : 'width';

  if (!arrowElement || !popperOffsets) {
    return;
  }

  var paddingObject = toPaddingObject(options.padding, state);
  var arrowRect = getLayoutRect(arrowElement);
  var minProp = axis === 'y' ? top : left;
  var maxProp = axis === 'y' ? bottom : right;
  var endDiff = state.rects.reference[len] + state.rects.reference[axis] - popperOffsets[axis] - state.rects.popper[len];
  var startDiff = popperOffsets[axis] - state.rects.reference[axis];
  var arrowOffsetParent = getOffsetParent(arrowElement);
  var clientSize = arrowOffsetParent ? axis === 'y' ? arrowOffsetParent.clientHeight || 0 : arrowOffsetParent.clientWidth || 0 : 0;
  var centerToReference = endDiff / 2 - startDiff / 2; // Make sure the arrow doesn't overflow the popper if the center point is
  // outside of the popper bounds

  var min = paddingObject[minProp];
  var max = clientSize - arrowRect[len] - paddingObject[maxProp];
  var center = clientSize / 2 - arrowRect[len] / 2 + centerToReference;
  var offset = within(min, center, max); // Prevents breaking syntax highlighting...

  var axisProp = axis;
  state.modifiersData[name] = (_state$modifiersData$ = {}, _state$modifiersData$[axisProp] = offset, _state$modifiersData$.centerOffset = offset - center, _state$modifiersData$);
}

function effect$1(_ref2) {
  var state = _ref2.state,
      options = _ref2.options;
  var _options$element = options.element,
      arrowElement = _options$element === void 0 ? '[data-popper-arrow]' : _options$element;

  if (arrowElement == null) {
    return;
  } // CSS selector


  if (typeof arrowElement === 'string') {
    arrowElement = state.elements.popper.querySelector(arrowElement);

    if (!arrowElement) {
      return;
    }
  }

  if (!contains(state.elements.popper, arrowElement)) {
    return;
  }

  state.elements.arrow = arrowElement;
} // eslint-disable-next-line import/no-unused-modules


var arrow$1 = {
  name: 'arrow',
  enabled: true,
  phase: 'main',
  fn: arrow,
  effect: effect$1,
  requires: ['popperOffsets'],
  requiresIfExists: ['preventOverflow']
};

function getVariation(placement) {
  return placement.split('-')[1];
}

var unsetSides = {
  top: 'auto',
  right: 'auto',
  bottom: 'auto',
  left: 'auto'
}; // Round the offsets to the nearest suitable subpixel based on the DPR.
// Zooming can change the DPR, but it seems to report a value that will
// cleanly divide the values into the appropriate subpixels.

function roundOffsetsByDPR(_ref, win) {
  var x = _ref.x,
      y = _ref.y;
  var dpr = win.devicePixelRatio || 1;
  return {
    x: round(x * dpr) / dpr || 0,
    y: round(y * dpr) / dpr || 0
  };
}

function mapToStyles(_ref2) {
  var _Object$assign2;

  var popper = _ref2.popper,
      popperRect = _ref2.popperRect,
      placement = _ref2.placement,
      variation = _ref2.variation,
      offsets = _ref2.offsets,
      position = _ref2.position,
      gpuAcceleration = _ref2.gpuAcceleration,
      adaptive = _ref2.adaptive,
      roundOffsets = _ref2.roundOffsets,
      isFixed = _ref2.isFixed;
  var _offsets$x = offsets.x,
      x = _offsets$x === void 0 ? 0 : _offsets$x,
      _offsets$y = offsets.y,
      y = _offsets$y === void 0 ? 0 : _offsets$y;

  var _ref3 = typeof roundOffsets === 'function' ? roundOffsets({
    x: x,
    y: y
  }) : {
    x: x,
    y: y
  };

  x = _ref3.x;
  y = _ref3.y;
  var hasX = offsets.hasOwnProperty('x');
  var hasY = offsets.hasOwnProperty('y');
  var sideX = left;
  var sideY = top;
  var win = window;

  if (adaptive) {
    var offsetParent = getOffsetParent(popper);
    var heightProp = 'clientHeight';
    var widthProp = 'clientWidth';

    if (offsetParent === getWindow(popper)) {
      offsetParent = getDocumentElement(popper);

      if (getComputedStyle$1(offsetParent).position !== 'static' && position === 'absolute') {
        heightProp = 'scrollHeight';
        widthProp = 'scrollWidth';
      }
    } // $FlowFixMe[incompatible-cast]: force type refinement, we compare offsetParent with window above, but Flow doesn't detect it


    offsetParent = offsetParent;

    if (placement === top || (placement === left || placement === right) && variation === end) {
      sideY = bottom;
      var offsetY = isFixed && offsetParent === win && win.visualViewport ? win.visualViewport.height : // $FlowFixMe[prop-missing]
      offsetParent[heightProp];
      y -= offsetY - popperRect.height;
      y *= gpuAcceleration ? 1 : -1;
    }

    if (placement === left || (placement === top || placement === bottom) && variation === end) {
      sideX = right;
      var offsetX = isFixed && offsetParent === win && win.visualViewport ? win.visualViewport.width : // $FlowFixMe[prop-missing]
      offsetParent[widthProp];
      x -= offsetX - popperRect.width;
      x *= gpuAcceleration ? 1 : -1;
    }
  }

  var commonStyles = Object.assign({
    position: position
  }, adaptive && unsetSides);

  var _ref4 = roundOffsets === true ? roundOffsetsByDPR({
    x: x,
    y: y
  }, getWindow(popper)) : {
    x: x,
    y: y
  };

  x = _ref4.x;
  y = _ref4.y;

  if (gpuAcceleration) {
    var _Object$assign;

    return Object.assign({}, commonStyles, (_Object$assign = {}, _Object$assign[sideY] = hasY ? '0' : '', _Object$assign[sideX] = hasX ? '0' : '', _Object$assign.transform = (win.devicePixelRatio || 1) <= 1 ? "translate(" + x + "px, " + y + "px)" : "translate3d(" + x + "px, " + y + "px, 0)", _Object$assign));
  }

  return Object.assign({}, commonStyles, (_Object$assign2 = {}, _Object$assign2[sideY] = hasY ? y + "px" : '', _Object$assign2[sideX] = hasX ? x + "px" : '', _Object$assign2.transform = '', _Object$assign2));
}

function computeStyles(_ref5) {
  var state = _ref5.state,
      options = _ref5.options;
  var _options$gpuAccelerat = options.gpuAcceleration,
      gpuAcceleration = _options$gpuAccelerat === void 0 ? true : _options$gpuAccelerat,
      _options$adaptive = options.adaptive,
      adaptive = _options$adaptive === void 0 ? true : _options$adaptive,
      _options$roundOffsets = options.roundOffsets,
      roundOffsets = _options$roundOffsets === void 0 ? true : _options$roundOffsets;
  var commonStyles = {
    placement: getBasePlacement(state.placement),
    variation: getVariation(state.placement),
    popper: state.elements.popper,
    popperRect: state.rects.popper,
    gpuAcceleration: gpuAcceleration,
    isFixed: state.options.strategy === 'fixed'
  };

  if (state.modifiersData.popperOffsets != null) {
    state.styles.popper = Object.assign({}, state.styles.popper, mapToStyles(Object.assign({}, commonStyles, {
      offsets: state.modifiersData.popperOffsets,
      position: state.options.strategy,
      adaptive: adaptive,
      roundOffsets: roundOffsets
    })));
  }

  if (state.modifiersData.arrow != null) {
    state.styles.arrow = Object.assign({}, state.styles.arrow, mapToStyles(Object.assign({}, commonStyles, {
      offsets: state.modifiersData.arrow,
      position: 'absolute',
      adaptive: false,
      roundOffsets: roundOffsets
    })));
  }

  state.attributes.popper = Object.assign({}, state.attributes.popper, {
    'data-popper-placement': state.placement
  });
} // eslint-disable-next-line import/no-unused-modules


var computeStyles$1 = {
  name: 'computeStyles',
  enabled: true,
  phase: 'beforeWrite',
  fn: computeStyles,
  data: {}
};

var passive = {
  passive: true
};

function effect(_ref) {
  var state = _ref.state,
      instance = _ref.instance,
      options = _ref.options;
  var _options$scroll = options.scroll,
      scroll = _options$scroll === void 0 ? true : _options$scroll,
      _options$resize = options.resize,
      resize = _options$resize === void 0 ? true : _options$resize;
  var window = getWindow(state.elements.popper);
  var scrollParents = [].concat(state.scrollParents.reference, state.scrollParents.popper);

  if (scroll) {
    scrollParents.forEach(function (scrollParent) {
      scrollParent.addEventListener('scroll', instance.update, passive);
    });
  }

  if (resize) {
    window.addEventListener('resize', instance.update, passive);
  }

  return function () {
    if (scroll) {
      scrollParents.forEach(function (scrollParent) {
        scrollParent.removeEventListener('scroll', instance.update, passive);
      });
    }

    if (resize) {
      window.removeEventListener('resize', instance.update, passive);
    }
  };
} // eslint-disable-next-line import/no-unused-modules


var eventListeners = {
  name: 'eventListeners',
  enabled: true,
  phase: 'write',
  fn: function fn() {},
  effect: effect,
  data: {}
};

var hash$1 = {
  left: 'right',
  right: 'left',
  bottom: 'top',
  top: 'bottom'
};
function getOppositePlacement(placement) {
  return placement.replace(/left|right|bottom|top/g, function (matched) {
    return hash$1[matched];
  });
}

var hash = {
  start: 'end',
  end: 'start'
};
function getOppositeVariationPlacement(placement) {
  return placement.replace(/start|end/g, function (matched) {
    return hash[matched];
  });
}

function getWindowScroll(node) {
  var win = getWindow(node);
  var scrollLeft = win.pageXOffset;
  var scrollTop = win.pageYOffset;
  return {
    scrollLeft: scrollLeft,
    scrollTop: scrollTop
  };
}

function getWindowScrollBarX(element) {
  // If <html> has a CSS width greater than the viewport, then this will be
  // incorrect for RTL.
  // Popper 1 is broken in this case and never had a bug report so let's assume
  // it's not an issue. I don't think anyone ever specifies width on <html>
  // anyway.
  // Browsers where the left scrollbar doesn't cause an issue report `0` for
  // this (e.g. Edge 2019, IE11, Safari)
  return getBoundingClientRect(getDocumentElement(element)).left + getWindowScroll(element).scrollLeft;
}

function getViewportRect(element, strategy) {
  var win = getWindow(element);
  var html = getDocumentElement(element);
  var visualViewport = win.visualViewport;
  var width = html.clientWidth;
  var height = html.clientHeight;
  var x = 0;
  var y = 0;

  if (visualViewport) {
    width = visualViewport.width;
    height = visualViewport.height;
    var layoutViewport = isLayoutViewport();

    if (layoutViewport || !layoutViewport && strategy === 'fixed') {
      x = visualViewport.offsetLeft;
      y = visualViewport.offsetTop;
    }
  }

  return {
    width: width,
    height: height,
    x: x + getWindowScrollBarX(element),
    y: y
  };
}

// of the `<html>` and `<body>` rect bounds if horizontally scrollable

function getDocumentRect(element) {
  var _element$ownerDocumen;

  var html = getDocumentElement(element);
  var winScroll = getWindowScroll(element);
  var body = (_element$ownerDocumen = element.ownerDocument) == null ? void 0 : _element$ownerDocumen.body;
  var width = max(html.scrollWidth, html.clientWidth, body ? body.scrollWidth : 0, body ? body.clientWidth : 0);
  var height = max(html.scrollHeight, html.clientHeight, body ? body.scrollHeight : 0, body ? body.clientHeight : 0);
  var x = -winScroll.scrollLeft + getWindowScrollBarX(element);
  var y = -winScroll.scrollTop;

  if (getComputedStyle$1(body || html).direction === 'rtl') {
    x += max(html.clientWidth, body ? body.clientWidth : 0) - width;
  }

  return {
    width: width,
    height: height,
    x: x,
    y: y
  };
}

function isScrollParent(element) {
  // Firefox wants us to check `-x` and `-y` variations as well
  var _getComputedStyle = getComputedStyle$1(element),
      overflow = _getComputedStyle.overflow,
      overflowX = _getComputedStyle.overflowX,
      overflowY = _getComputedStyle.overflowY;

  return /auto|scroll|overlay|hidden/.test(overflow + overflowY + overflowX);
}

function getScrollParent(node) {
  if (['html', 'body', '#document'].indexOf(getNodeName(node)) >= 0) {
    // $FlowFixMe[incompatible-return]: assume body is always available
    return node.ownerDocument.body;
  }

  if (isHTMLElement(node) && isScrollParent(node)) {
    return node;
  }

  return getScrollParent(getParentNode(node));
}

/*
given a DOM element, return the list of all scroll parents, up the list of ancesors
until we get to the top window object. This list is what we attach scroll listeners
to, because if any of these parent elements scroll, we'll need to re-calculate the
reference element's position.
*/

function listScrollParents(element, list) {
  var _element$ownerDocumen;

  if (list === void 0) {
    list = [];
  }

  var scrollParent = getScrollParent(element);
  var isBody = scrollParent === ((_element$ownerDocumen = element.ownerDocument) == null ? void 0 : _element$ownerDocumen.body);
  var win = getWindow(scrollParent);
  var target = isBody ? [win].concat(win.visualViewport || [], isScrollParent(scrollParent) ? scrollParent : []) : scrollParent;
  var updatedList = list.concat(target);
  return isBody ? updatedList : // $FlowFixMe[incompatible-call]: isBody tells us target will be an HTMLElement here
  updatedList.concat(listScrollParents(getParentNode(target)));
}

function rectToClientRect(rect) {
  return Object.assign({}, rect, {
    left: rect.x,
    top: rect.y,
    right: rect.x + rect.width,
    bottom: rect.y + rect.height
  });
}

function getInnerBoundingClientRect(element, strategy) {
  var rect = getBoundingClientRect(element, false, strategy === 'fixed');
  rect.top = rect.top + element.clientTop;
  rect.left = rect.left + element.clientLeft;
  rect.bottom = rect.top + element.clientHeight;
  rect.right = rect.left + element.clientWidth;
  rect.width = element.clientWidth;
  rect.height = element.clientHeight;
  rect.x = rect.left;
  rect.y = rect.top;
  return rect;
}

function getClientRectFromMixedType(element, clippingParent, strategy) {
  return clippingParent === viewport ? rectToClientRect(getViewportRect(element, strategy)) : isElement(clippingParent) ? getInnerBoundingClientRect(clippingParent, strategy) : rectToClientRect(getDocumentRect(getDocumentElement(element)));
} // A "clipping parent" is an overflowable container with the characteristic of
// clipping (or hiding) overflowing elements with a position different from
// `initial`


function getClippingParents(element) {
  var clippingParents = listScrollParents(getParentNode(element));
  var canEscapeClipping = ['absolute', 'fixed'].indexOf(getComputedStyle$1(element).position) >= 0;
  var clipperElement = canEscapeClipping && isHTMLElement(element) ? getOffsetParent(element) : element;

  if (!isElement(clipperElement)) {
    return [];
  } // $FlowFixMe[incompatible-return]: https://github.com/facebook/flow/issues/1414


  return clippingParents.filter(function (clippingParent) {
    return isElement(clippingParent) && contains(clippingParent, clipperElement) && getNodeName(clippingParent) !== 'body';
  });
} // Gets the maximum area that the element is visible in due to any number of
// clipping parents


function getClippingRect(element, boundary, rootBoundary, strategy) {
  var mainClippingParents = boundary === 'clippingParents' ? getClippingParents(element) : [].concat(boundary);
  var clippingParents = [].concat(mainClippingParents, [rootBoundary]);
  var firstClippingParent = clippingParents[0];
  var clippingRect = clippingParents.reduce(function (accRect, clippingParent) {
    var rect = getClientRectFromMixedType(element, clippingParent, strategy);
    accRect.top = max(rect.top, accRect.top);
    accRect.right = min(rect.right, accRect.right);
    accRect.bottom = min(rect.bottom, accRect.bottom);
    accRect.left = max(rect.left, accRect.left);
    return accRect;
  }, getClientRectFromMixedType(element, firstClippingParent, strategy));
  clippingRect.width = clippingRect.right - clippingRect.left;
  clippingRect.height = clippingRect.bottom - clippingRect.top;
  clippingRect.x = clippingRect.left;
  clippingRect.y = clippingRect.top;
  return clippingRect;
}

function computeOffsets(_ref) {
  var reference = _ref.reference,
      element = _ref.element,
      placement = _ref.placement;
  var basePlacement = placement ? getBasePlacement(placement) : null;
  var variation = placement ? getVariation(placement) : null;
  var commonX = reference.x + reference.width / 2 - element.width / 2;
  var commonY = reference.y + reference.height / 2 - element.height / 2;
  var offsets;

  switch (basePlacement) {
    case top:
      offsets = {
        x: commonX,
        y: reference.y - element.height
      };
      break;

    case bottom:
      offsets = {
        x: commonX,
        y: reference.y + reference.height
      };
      break;

    case right:
      offsets = {
        x: reference.x + reference.width,
        y: commonY
      };
      break;

    case left:
      offsets = {
        x: reference.x - element.width,
        y: commonY
      };
      break;

    default:
      offsets = {
        x: reference.x,
        y: reference.y
      };
  }

  var mainAxis = basePlacement ? getMainAxisFromPlacement(basePlacement) : null;

  if (mainAxis != null) {
    var len = mainAxis === 'y' ? 'height' : 'width';

    switch (variation) {
      case start:
        offsets[mainAxis] = offsets[mainAxis] - (reference[len] / 2 - element[len] / 2);
        break;

      case end:
        offsets[mainAxis] = offsets[mainAxis] + (reference[len] / 2 - element[len] / 2);
        break;
    }
  }

  return offsets;
}

function detectOverflow(state, options) {
  if (options === void 0) {
    options = {};
  }

  var _options = options,
      _options$placement = _options.placement,
      placement = _options$placement === void 0 ? state.placement : _options$placement,
      _options$strategy = _options.strategy,
      strategy = _options$strategy === void 0 ? state.strategy : _options$strategy,
      _options$boundary = _options.boundary,
      boundary = _options$boundary === void 0 ? clippingParents : _options$boundary,
      _options$rootBoundary = _options.rootBoundary,
      rootBoundary = _options$rootBoundary === void 0 ? viewport : _options$rootBoundary,
      _options$elementConte = _options.elementContext,
      elementContext = _options$elementConte === void 0 ? popper : _options$elementConte,
      _options$altBoundary = _options.altBoundary,
      altBoundary = _options$altBoundary === void 0 ? false : _options$altBoundary,
      _options$padding = _options.padding,
      padding = _options$padding === void 0 ? 0 : _options$padding;
  var paddingObject = mergePaddingObject(typeof padding !== 'number' ? padding : expandToHashMap(padding, basePlacements));
  var altContext = elementContext === popper ? reference : popper;
  var popperRect = state.rects.popper;
  var element = state.elements[altBoundary ? altContext : elementContext];
  var clippingClientRect = getClippingRect(isElement(element) ? element : element.contextElement || getDocumentElement(state.elements.popper), boundary, rootBoundary, strategy);
  var referenceClientRect = getBoundingClientRect(state.elements.reference);
  var popperOffsets = computeOffsets({
    reference: referenceClientRect,
    element: popperRect,
    strategy: 'absolute',
    placement: placement
  });
  var popperClientRect = rectToClientRect(Object.assign({}, popperRect, popperOffsets));
  var elementClientRect = elementContext === popper ? popperClientRect : referenceClientRect; // positive = overflowing the clipping rect
  // 0 or negative = within the clipping rect

  var overflowOffsets = {
    top: clippingClientRect.top - elementClientRect.top + paddingObject.top,
    bottom: elementClientRect.bottom - clippingClientRect.bottom + paddingObject.bottom,
    left: clippingClientRect.left - elementClientRect.left + paddingObject.left,
    right: elementClientRect.right - clippingClientRect.right + paddingObject.right
  };
  var offsetData = state.modifiersData.offset; // Offsets can be applied only to the popper element

  if (elementContext === popper && offsetData) {
    var offset = offsetData[placement];
    Object.keys(overflowOffsets).forEach(function (key) {
      var multiply = [right, bottom].indexOf(key) >= 0 ? 1 : -1;
      var axis = [top, bottom].indexOf(key) >= 0 ? 'y' : 'x';
      overflowOffsets[key] += offset[axis] * multiply;
    });
  }

  return overflowOffsets;
}

function computeAutoPlacement(state, options) {
  if (options === void 0) {
    options = {};
  }

  var _options = options,
      placement = _options.placement,
      boundary = _options.boundary,
      rootBoundary = _options.rootBoundary,
      padding = _options.padding,
      flipVariations = _options.flipVariations,
      _options$allowedAutoP = _options.allowedAutoPlacements,
      allowedAutoPlacements = _options$allowedAutoP === void 0 ? placements : _options$allowedAutoP;
  var variation = getVariation(placement);
  var placements$1 = variation ? flipVariations ? variationPlacements : variationPlacements.filter(function (placement) {
    return getVariation(placement) === variation;
  }) : basePlacements;
  var allowedPlacements = placements$1.filter(function (placement) {
    return allowedAutoPlacements.indexOf(placement) >= 0;
  });

  if (allowedPlacements.length === 0) {
    allowedPlacements = placements$1;
  } // $FlowFixMe[incompatible-type]: Flow seems to have problems with two array unions...


  var overflows = allowedPlacements.reduce(function (acc, placement) {
    acc[placement] = detectOverflow(state, {
      placement: placement,
      boundary: boundary,
      rootBoundary: rootBoundary,
      padding: padding
    })[getBasePlacement(placement)];
    return acc;
  }, {});
  return Object.keys(overflows).sort(function (a, b) {
    return overflows[a] - overflows[b];
  });
}

function getExpandedFallbackPlacements(placement) {
  if (getBasePlacement(placement) === auto) {
    return [];
  }

  var oppositePlacement = getOppositePlacement(placement);
  return [getOppositeVariationPlacement(placement), oppositePlacement, getOppositeVariationPlacement(oppositePlacement)];
}

function flip(_ref) {
  var state = _ref.state,
      options = _ref.options,
      name = _ref.name;

  if (state.modifiersData[name]._skip) {
    return;
  }

  var _options$mainAxis = options.mainAxis,
      checkMainAxis = _options$mainAxis === void 0 ? true : _options$mainAxis,
      _options$altAxis = options.altAxis,
      checkAltAxis = _options$altAxis === void 0 ? true : _options$altAxis,
      specifiedFallbackPlacements = options.fallbackPlacements,
      padding = options.padding,
      boundary = options.boundary,
      rootBoundary = options.rootBoundary,
      altBoundary = options.altBoundary,
      _options$flipVariatio = options.flipVariations,
      flipVariations = _options$flipVariatio === void 0 ? true : _options$flipVariatio,
      allowedAutoPlacements = options.allowedAutoPlacements;
  var preferredPlacement = state.options.placement;
  var basePlacement = getBasePlacement(preferredPlacement);
  var isBasePlacement = basePlacement === preferredPlacement;
  var fallbackPlacements = specifiedFallbackPlacements || (isBasePlacement || !flipVariations ? [getOppositePlacement(preferredPlacement)] : getExpandedFallbackPlacements(preferredPlacement));
  var placements = [preferredPlacement].concat(fallbackPlacements).reduce(function (acc, placement) {
    return acc.concat(getBasePlacement(placement) === auto ? computeAutoPlacement(state, {
      placement: placement,
      boundary: boundary,
      rootBoundary: rootBoundary,
      padding: padding,
      flipVariations: flipVariations,
      allowedAutoPlacements: allowedAutoPlacements
    }) : placement);
  }, []);
  var referenceRect = state.rects.reference;
  var popperRect = state.rects.popper;
  var checksMap = new Map();
  var makeFallbackChecks = true;
  var firstFittingPlacement = placements[0];

  for (var i = 0; i < placements.length; i++) {
    var placement = placements[i];

    var _basePlacement = getBasePlacement(placement);

    var isStartVariation = getVariation(placement) === start;
    var isVertical = [top, bottom].indexOf(_basePlacement) >= 0;
    var len = isVertical ? 'width' : 'height';
    var overflow = detectOverflow(state, {
      placement: placement,
      boundary: boundary,
      rootBoundary: rootBoundary,
      altBoundary: altBoundary,
      padding: padding
    });
    var mainVariationSide = isVertical ? isStartVariation ? right : left : isStartVariation ? bottom : top;

    if (referenceRect[len] > popperRect[len]) {
      mainVariationSide = getOppositePlacement(mainVariationSide);
    }

    var altVariationSide = getOppositePlacement(mainVariationSide);
    var checks = [];

    if (checkMainAxis) {
      checks.push(overflow[_basePlacement] <= 0);
    }

    if (checkAltAxis) {
      checks.push(overflow[mainVariationSide] <= 0, overflow[altVariationSide] <= 0);
    }

    if (checks.every(function (check) {
      return check;
    })) {
      firstFittingPlacement = placement;
      makeFallbackChecks = false;
      break;
    }

    checksMap.set(placement, checks);
  }

  if (makeFallbackChecks) {
    // `2` may be desired in some cases – research later
    var numberOfChecks = flipVariations ? 3 : 1;

    var _loop = function _loop(_i) {
      var fittingPlacement = placements.find(function (placement) {
        var checks = checksMap.get(placement);

        if (checks) {
          return checks.slice(0, _i).every(function (check) {
            return check;
          });
        }
      });

      if (fittingPlacement) {
        firstFittingPlacement = fittingPlacement;
        return "break";
      }
    };

    for (var _i = numberOfChecks; _i > 0; _i--) {
      var _ret = _loop(_i);

      if (_ret === "break") break;
    }
  }

  if (state.placement !== firstFittingPlacement) {
    state.modifiersData[name]._skip = true;
    state.placement = firstFittingPlacement;
    state.reset = true;
  }
} // eslint-disable-next-line import/no-unused-modules


var flip$1 = {
  name: 'flip',
  enabled: true,
  phase: 'main',
  fn: flip,
  requiresIfExists: ['offset'],
  data: {
    _skip: false
  }
};

function getSideOffsets(overflow, rect, preventedOffsets) {
  if (preventedOffsets === void 0) {
    preventedOffsets = {
      x: 0,
      y: 0
    };
  }

  return {
    top: overflow.top - rect.height - preventedOffsets.y,
    right: overflow.right - rect.width + preventedOffsets.x,
    bottom: overflow.bottom - rect.height + preventedOffsets.y,
    left: overflow.left - rect.width - preventedOffsets.x
  };
}

function isAnySideFullyClipped(overflow) {
  return [top, right, bottom, left].some(function (side) {
    return overflow[side] >= 0;
  });
}

function hide(_ref) {
  var state = _ref.state,
      name = _ref.name;
  var referenceRect = state.rects.reference;
  var popperRect = state.rects.popper;
  var preventedOffsets = state.modifiersData.preventOverflow;
  var referenceOverflow = detectOverflow(state, {
    elementContext: 'reference'
  });
  var popperAltOverflow = detectOverflow(state, {
    altBoundary: true
  });
  var referenceClippingOffsets = getSideOffsets(referenceOverflow, referenceRect);
  var popperEscapeOffsets = getSideOffsets(popperAltOverflow, popperRect, preventedOffsets);
  var isReferenceHidden = isAnySideFullyClipped(referenceClippingOffsets);
  var hasPopperEscaped = isAnySideFullyClipped(popperEscapeOffsets);
  state.modifiersData[name] = {
    referenceClippingOffsets: referenceClippingOffsets,
    popperEscapeOffsets: popperEscapeOffsets,
    isReferenceHidden: isReferenceHidden,
    hasPopperEscaped: hasPopperEscaped
  };
  state.attributes.popper = Object.assign({}, state.attributes.popper, {
    'data-popper-reference-hidden': isReferenceHidden,
    'data-popper-escaped': hasPopperEscaped
  });
} // eslint-disable-next-line import/no-unused-modules


var hide$1 = {
  name: 'hide',
  enabled: true,
  phase: 'main',
  requiresIfExists: ['preventOverflow'],
  fn: hide
};

function distanceAndSkiddingToXY(placement, rects, offset) {
  var basePlacement = getBasePlacement(placement);
  var invertDistance = [left, top].indexOf(basePlacement) >= 0 ? -1 : 1;

  var _ref = typeof offset === 'function' ? offset(Object.assign({}, rects, {
    placement: placement
  })) : offset,
      skidding = _ref[0],
      distance = _ref[1];

  skidding = skidding || 0;
  distance = (distance || 0) * invertDistance;
  return [left, right].indexOf(basePlacement) >= 0 ? {
    x: distance,
    y: skidding
  } : {
    x: skidding,
    y: distance
  };
}

function offset(_ref2) {
  var state = _ref2.state,
      options = _ref2.options,
      name = _ref2.name;
  var _options$offset = options.offset,
      offset = _options$offset === void 0 ? [0, 0] : _options$offset;
  var data = placements.reduce(function (acc, placement) {
    acc[placement] = distanceAndSkiddingToXY(placement, state.rects, offset);
    return acc;
  }, {});
  var _data$state$placement = data[state.placement],
      x = _data$state$placement.x,
      y = _data$state$placement.y;

  if (state.modifiersData.popperOffsets != null) {
    state.modifiersData.popperOffsets.x += x;
    state.modifiersData.popperOffsets.y += y;
  }

  state.modifiersData[name] = data;
} // eslint-disable-next-line import/no-unused-modules


var offset$1 = {
  name: 'offset',
  enabled: true,
  phase: 'main',
  requires: ['popperOffsets'],
  fn: offset
};

function popperOffsets(_ref) {
  var state = _ref.state,
      name = _ref.name;
  // Offsets are the actual position the popper needs to have to be
  // properly positioned near its reference element
  // This is the most basic placement, and will be adjusted by
  // the modifiers in the next step
  state.modifiersData[name] = computeOffsets({
    reference: state.rects.reference,
    element: state.rects.popper,
    strategy: 'absolute',
    placement: state.placement
  });
} // eslint-disable-next-line import/no-unused-modules


var popperOffsets$1 = {
  name: 'popperOffsets',
  enabled: true,
  phase: 'read',
  fn: popperOffsets,
  data: {}
};

function getAltAxis(axis) {
  return axis === 'x' ? 'y' : 'x';
}

function preventOverflow(_ref) {
  var state = _ref.state,
      options = _ref.options,
      name = _ref.name;
  var _options$mainAxis = options.mainAxis,
      checkMainAxis = _options$mainAxis === void 0 ? true : _options$mainAxis,
      _options$altAxis = options.altAxis,
      checkAltAxis = _options$altAxis === void 0 ? false : _options$altAxis,
      boundary = options.boundary,
      rootBoundary = options.rootBoundary,
      altBoundary = options.altBoundary,
      padding = options.padding,
      _options$tether = options.tether,
      tether = _options$tether === void 0 ? true : _options$tether,
      _options$tetherOffset = options.tetherOffset,
      tetherOffset = _options$tetherOffset === void 0 ? 0 : _options$tetherOffset;
  var overflow = detectOverflow(state, {
    boundary: boundary,
    rootBoundary: rootBoundary,
    padding: padding,
    altBoundary: altBoundary
  });
  var basePlacement = getBasePlacement(state.placement);
  var variation = getVariation(state.placement);
  var isBasePlacement = !variation;
  var mainAxis = getMainAxisFromPlacement(basePlacement);
  var altAxis = getAltAxis(mainAxis);
  var popperOffsets = state.modifiersData.popperOffsets;
  var referenceRect = state.rects.reference;
  var popperRect = state.rects.popper;
  var tetherOffsetValue = typeof tetherOffset === 'function' ? tetherOffset(Object.assign({}, state.rects, {
    placement: state.placement
  })) : tetherOffset;
  var normalizedTetherOffsetValue = typeof tetherOffsetValue === 'number' ? {
    mainAxis: tetherOffsetValue,
    altAxis: tetherOffsetValue
  } : Object.assign({
    mainAxis: 0,
    altAxis: 0
  }, tetherOffsetValue);
  var offsetModifierState = state.modifiersData.offset ? state.modifiersData.offset[state.placement] : null;
  var data = {
    x: 0,
    y: 0
  };

  if (!popperOffsets) {
    return;
  }

  if (checkMainAxis) {
    var _offsetModifierState$;

    var mainSide = mainAxis === 'y' ? top : left;
    var altSide = mainAxis === 'y' ? bottom : right;
    var len = mainAxis === 'y' ? 'height' : 'width';
    var offset = popperOffsets[mainAxis];
    var min$1 = offset + overflow[mainSide];
    var max$1 = offset - overflow[altSide];
    var additive = tether ? -popperRect[len] / 2 : 0;
    var minLen = variation === start ? referenceRect[len] : popperRect[len];
    var maxLen = variation === start ? -popperRect[len] : -referenceRect[len]; // We need to include the arrow in the calculation so the arrow doesn't go
    // outside the reference bounds

    var arrowElement = state.elements.arrow;
    var arrowRect = tether && arrowElement ? getLayoutRect(arrowElement) : {
      width: 0,
      height: 0
    };
    var arrowPaddingObject = state.modifiersData['arrow#persistent'] ? state.modifiersData['arrow#persistent'].padding : getFreshSideObject();
    var arrowPaddingMin = arrowPaddingObject[mainSide];
    var arrowPaddingMax = arrowPaddingObject[altSide]; // If the reference length is smaller than the arrow length, we don't want
    // to include its full size in the calculation. If the reference is small
    // and near the edge of a boundary, the popper can overflow even if the
    // reference is not overflowing as well (e.g. virtual elements with no
    // width or height)

    var arrowLen = within(0, referenceRect[len], arrowRect[len]);
    var minOffset = isBasePlacement ? referenceRect[len] / 2 - additive - arrowLen - arrowPaddingMin - normalizedTetherOffsetValue.mainAxis : minLen - arrowLen - arrowPaddingMin - normalizedTetherOffsetValue.mainAxis;
    var maxOffset = isBasePlacement ? -referenceRect[len] / 2 + additive + arrowLen + arrowPaddingMax + normalizedTetherOffsetValue.mainAxis : maxLen + arrowLen + arrowPaddingMax + normalizedTetherOffsetValue.mainAxis;
    var arrowOffsetParent = state.elements.arrow && getOffsetParent(state.elements.arrow);
    var clientOffset = arrowOffsetParent ? mainAxis === 'y' ? arrowOffsetParent.clientTop || 0 : arrowOffsetParent.clientLeft || 0 : 0;
    var offsetModifierValue = (_offsetModifierState$ = offsetModifierState == null ? void 0 : offsetModifierState[mainAxis]) != null ? _offsetModifierState$ : 0;
    var tetherMin = offset + minOffset - offsetModifierValue - clientOffset;
    var tetherMax = offset + maxOffset - offsetModifierValue;
    var preventedOffset = within(tether ? min(min$1, tetherMin) : min$1, offset, tether ? max(max$1, tetherMax) : max$1);
    popperOffsets[mainAxis] = preventedOffset;
    data[mainAxis] = preventedOffset - offset;
  }

  if (checkAltAxis) {
    var _offsetModifierState$2;

    var _mainSide = mainAxis === 'x' ? top : left;

    var _altSide = mainAxis === 'x' ? bottom : right;

    var _offset = popperOffsets[altAxis];

    var _len = altAxis === 'y' ? 'height' : 'width';

    var _min = _offset + overflow[_mainSide];

    var _max = _offset - overflow[_altSide];

    var isOriginSide = [top, left].indexOf(basePlacement) !== -1;

    var _offsetModifierValue = (_offsetModifierState$2 = offsetModifierState == null ? void 0 : offsetModifierState[altAxis]) != null ? _offsetModifierState$2 : 0;

    var _tetherMin = isOriginSide ? _min : _offset - referenceRect[_len] - popperRect[_len] - _offsetModifierValue + normalizedTetherOffsetValue.altAxis;

    var _tetherMax = isOriginSide ? _offset + referenceRect[_len] + popperRect[_len] - _offsetModifierValue - normalizedTetherOffsetValue.altAxis : _max;

    var _preventedOffset = tether && isOriginSide ? withinMaxClamp(_tetherMin, _offset, _tetherMax) : within(tether ? _tetherMin : _min, _offset, tether ? _tetherMax : _max);

    popperOffsets[altAxis] = _preventedOffset;
    data[altAxis] = _preventedOffset - _offset;
  }

  state.modifiersData[name] = data;
} // eslint-disable-next-line import/no-unused-modules


var preventOverflow$1 = {
  name: 'preventOverflow',
  enabled: true,
  phase: 'main',
  fn: preventOverflow,
  requiresIfExists: ['offset']
};

function getHTMLElementScroll(element) {
  return {
    scrollLeft: element.scrollLeft,
    scrollTop: element.scrollTop
  };
}

function getNodeScroll(node) {
  if (node === getWindow(node) || !isHTMLElement(node)) {
    return getWindowScroll(node);
  } else {
    return getHTMLElementScroll(node);
  }
}

function isElementScaled(element) {
  var rect = element.getBoundingClientRect();
  var scaleX = round(rect.width) / element.offsetWidth || 1;
  var scaleY = round(rect.height) / element.offsetHeight || 1;
  return scaleX !== 1 || scaleY !== 1;
} // Returns the composite rect of an element relative to its offsetParent.
// Composite means it takes into account transforms as well as layout.


function getCompositeRect(elementOrVirtualElement, offsetParent, isFixed) {
  if (isFixed === void 0) {
    isFixed = false;
  }

  var isOffsetParentAnElement = isHTMLElement(offsetParent);
  var offsetParentIsScaled = isHTMLElement(offsetParent) && isElementScaled(offsetParent);
  var documentElement = getDocumentElement(offsetParent);
  var rect = getBoundingClientRect(elementOrVirtualElement, offsetParentIsScaled, isFixed);
  var scroll = {
    scrollLeft: 0,
    scrollTop: 0
  };
  var offsets = {
    x: 0,
    y: 0
  };

  if (isOffsetParentAnElement || !isOffsetParentAnElement && !isFixed) {
    if (getNodeName(offsetParent) !== 'body' || // https://github.com/popperjs/popper-core/issues/1078
    isScrollParent(documentElement)) {
      scroll = getNodeScroll(offsetParent);
    }

    if (isHTMLElement(offsetParent)) {
      offsets = getBoundingClientRect(offsetParent, true);
      offsets.x += offsetParent.clientLeft;
      offsets.y += offsetParent.clientTop;
    } else if (documentElement) {
      offsets.x = getWindowScrollBarX(documentElement);
    }
  }

  return {
    x: rect.left + scroll.scrollLeft - offsets.x,
    y: rect.top + scroll.scrollTop - offsets.y,
    width: rect.width,
    height: rect.height
  };
}

function order(modifiers) {
  var map = new Map();
  var visited = new Set();
  var result = [];
  modifiers.forEach(function (modifier) {
    map.set(modifier.name, modifier);
  }); // On visiting object, check for its dependencies and visit them recursively

  function sort(modifier) {
    visited.add(modifier.name);
    var requires = [].concat(modifier.requires || [], modifier.requiresIfExists || []);
    requires.forEach(function (dep) {
      if (!visited.has(dep)) {
        var depModifier = map.get(dep);

        if (depModifier) {
          sort(depModifier);
        }
      }
    });
    result.push(modifier);
  }

  modifiers.forEach(function (modifier) {
    if (!visited.has(modifier.name)) {
      // check for visited object
      sort(modifier);
    }
  });
  return result;
}

function orderModifiers(modifiers) {
  // order based on dependencies
  var orderedModifiers = order(modifiers); // order based on phase

  return modifierPhases.reduce(function (acc, phase) {
    return acc.concat(orderedModifiers.filter(function (modifier) {
      return modifier.phase === phase;
    }));
  }, []);
}

function debounce(fn) {
  var pending;
  return function () {
    if (!pending) {
      pending = new Promise(function (resolve) {
        Promise.resolve().then(function () {
          pending = undefined;
          resolve(fn());
        });
      });
    }

    return pending;
  };
}

function mergeByName(modifiers) {
  var merged = modifiers.reduce(function (merged, current) {
    var existing = merged[current.name];
    merged[current.name] = existing ? Object.assign({}, existing, current, {
      options: Object.assign({}, existing.options, current.options),
      data: Object.assign({}, existing.data, current.data)
    }) : current;
    return merged;
  }, {}); // IE11 does not support Object.values

  return Object.keys(merged).map(function (key) {
    return merged[key];
  });
}

var DEFAULT_OPTIONS = {
  placement: 'bottom',
  modifiers: [],
  strategy: 'absolute'
};

function areValidElements() {
  for (var _len = arguments.length, args = new Array(_len), _key = 0; _key < _len; _key++) {
    args[_key] = arguments[_key];
  }

  return !args.some(function (element) {
    return !(element && typeof element.getBoundingClientRect === 'function');
  });
}

function popperGenerator(generatorOptions) {
  if (generatorOptions === void 0) {
    generatorOptions = {};
  }

  var _generatorOptions = generatorOptions,
      _generatorOptions$def = _generatorOptions.defaultModifiers,
      defaultModifiers = _generatorOptions$def === void 0 ? [] : _generatorOptions$def,
      _generatorOptions$def2 = _generatorOptions.defaultOptions,
      defaultOptions = _generatorOptions$def2 === void 0 ? DEFAULT_OPTIONS : _generatorOptions$def2;
  return function createPopper(reference, popper, options) {
    if (options === void 0) {
      options = defaultOptions;
    }

    var state = {
      placement: 'bottom',
      orderedModifiers: [],
      options: Object.assign({}, DEFAULT_OPTIONS, defaultOptions),
      modifiersData: {},
      elements: {
        reference: reference,
        popper: popper
      },
      attributes: {},
      styles: {}
    };
    var effectCleanupFns = [];
    var isDestroyed = false;
    var instance = {
      state: state,
      setOptions: function setOptions(setOptionsAction) {
        var options = typeof setOptionsAction === 'function' ? setOptionsAction(state.options) : setOptionsAction;
        cleanupModifierEffects();
        state.options = Object.assign({}, defaultOptions, state.options, options);
        state.scrollParents = {
          reference: isElement(reference) ? listScrollParents(reference) : reference.contextElement ? listScrollParents(reference.contextElement) : [],
          popper: listScrollParents(popper)
        }; // Orders the modifiers based on their dependencies and `phase`
        // properties

        var orderedModifiers = orderModifiers(mergeByName([].concat(defaultModifiers, state.options.modifiers))); // Strip out disabled modifiers

        state.orderedModifiers = orderedModifiers.filter(function (m) {
          return m.enabled;
        });
        runModifierEffects();
        return instance.update();
      },
      // Sync update – it will always be executed, even if not necessary. This
      // is useful for low frequency updates where sync behavior simplifies the
      // logic.
      // For high frequency updates (e.g. `resize` and `scroll` events), always
      // prefer the async Popper#update method
      forceUpdate: function forceUpdate() {
        if (isDestroyed) {
          return;
        }

        var _state$elements = state.elements,
            reference = _state$elements.reference,
            popper = _state$elements.popper; // Don't proceed if `reference` or `popper` are not valid elements
        // anymore

        if (!areValidElements(reference, popper)) {
          return;
        } // Store the reference and popper rects to be read by modifiers


        state.rects = {
          reference: getCompositeRect(reference, getOffsetParent(popper), state.options.strategy === 'fixed'),
          popper: getLayoutRect(popper)
        }; // Modifiers have the ability to reset the current update cycle. The
        // most common use case for this is the `flip` modifier changing the
        // placement, which then needs to re-run all the modifiers, because the
        // logic was previously ran for the previous placement and is therefore
        // stale/incorrect

        state.reset = false;
        state.placement = state.options.placement; // On each update cycle, the `modifiersData` property for each modifier
        // is filled with the initial data specified by the modifier. This means
        // it doesn't persist and is fresh on each update.
        // To ensure persistent data, use `${name}#persistent`

        state.orderedModifiers.forEach(function (modifier) {
          return state.modifiersData[modifier.name] = Object.assign({}, modifier.data);
        });

        for (var index = 0; index < state.orderedModifiers.length; index++) {
          if (state.reset === true) {
            state.reset = false;
            index = -1;
            continue;
          }

          var _state$orderedModifie = state.orderedModifiers[index],
              fn = _state$orderedModifie.fn,
              _state$orderedModifie2 = _state$orderedModifie.options,
              _options = _state$orderedModifie2 === void 0 ? {} : _state$orderedModifie2,
              name = _state$orderedModifie.name;

          if (typeof fn === 'function') {
            state = fn({
              state: state,
              options: _options,
              name: name,
              instance: instance
            }) || state;
          }
        }
      },
      // Async and optimistically optimized update – it will not be executed if
      // not necessary (debounced to run at most once-per-tick)
      update: debounce(function () {
        return new Promise(function (resolve) {
          instance.forceUpdate();
          resolve(state);
        });
      }),
      destroy: function destroy() {
        cleanupModifierEffects();
        isDestroyed = true;
      }
    };

    if (!areValidElements(reference, popper)) {
      return instance;
    }

    instance.setOptions(options).then(function (state) {
      if (!isDestroyed && options.onFirstUpdate) {
        options.onFirstUpdate(state);
      }
    }); // Modifiers have the ability to execute arbitrary code before the first
    // update cycle runs. They will be executed in the same order as the update
    // cycle. This is useful when a modifier adds some persistent data that
    // other modifiers need to use, but the modifier is run after the dependent
    // one.

    function runModifierEffects() {
      state.orderedModifiers.forEach(function (_ref) {
        var name = _ref.name,
            _ref$options = _ref.options,
            options = _ref$options === void 0 ? {} : _ref$options,
            effect = _ref.effect;

        if (typeof effect === 'function') {
          var cleanupFn = effect({
            state: state,
            name: name,
            instance: instance,
            options: options
          });

          var noopFn = function noopFn() {};

          effectCleanupFns.push(cleanupFn || noopFn);
        }
      });
    }

    function cleanupModifierEffects() {
      effectCleanupFns.forEach(function (fn) {
        return fn();
      });
      effectCleanupFns = [];
    }

    return instance;
  };
}

var defaultModifiers = [eventListeners, popperOffsets$1, computeStyles$1, applyStyles$1, offset$1, flip$1, preventOverflow$1, arrow$1, hide$1];
var createPopper = /*#__PURE__*/popperGenerator({
  defaultModifiers: defaultModifiers
}); // eslint-disable-next-line import/no-unused-modules

var getTransitionDurationFromElement = function (element) {
    if (!element) {
        return 0;
    }
    // Get transition-duration of the element
    var _a = window.getComputedStyle(element), transitionDuration = _a.transitionDuration, transitionDelay = _a.transitionDelay;
    var floatTransitionDuration = Number.parseFloat(transitionDuration);
    var floatTransitionDelay = Number.parseFloat(transitionDelay);
    // Return 0 if element or transition duration is not found
    if (!floatTransitionDuration && !floatTransitionDelay) {
        return 0;
    }
    // If multiple durations are defined, take the first
    transitionDuration = transitionDuration.split(',')[0];
    transitionDelay = transitionDelay.split(',')[0];
    return (Number.parseFloat(transitionDuration) + Number.parseFloat(transitionDelay)) * 1000;
};

var execute = function (callback) {
    if (typeof callback === 'function') {
        callback();
    }
};
var triggerTransitionEnd = function (element) {
    element.dispatchEvent(new Event('transitionend'));
};
var executeAfterTransition = function (callback, transitionElement, waitForTransition) {
    if (waitForTransition === void 0) { waitForTransition = true; }
    if (!waitForTransition) {
        execute(callback);
        return;
    }
    var durationPadding = 5;
    var emulatedDuration = getTransitionDurationFromElement(transitionElement) + durationPadding;
    var called = false;
    var handler = function (_a) {
        var target = _a.target;
        if (target !== transitionElement) {
            return;
        }
        called = true;
        transitionElement.removeEventListener('transitionend', handler);
        execute(callback);
    };
    transitionElement.addEventListener('transitionend', handler);
    setTimeout(function () {
        if (!called) {
            triggerTransitionEnd(transitionElement);
        }
    }, emulatedDuration);
};

var isRTL = function (element) {
    if (typeof document !== 'undefined' && document.documentElement.dir === 'rtl') {
        return true;
    }
    if (element) {
        return element.closest('[dir="rtl"]') !== null;
    }
    return false;
};

var getRTLPlacement = function (placement, element) {
    switch (placement) {
        case 'right': {
            return isRTL(element) ? 'left' : 'right';
        }
        case 'left': {
            return isRTL(element) ? 'right' : 'left';
        }
        default: {
            return placement;
        }
    }
};

var isInViewport = function (element) {
    var rect = element.getBoundingClientRect();
    return (Math.floor(rect.top) >= 0 &&
        Math.floor(rect.left) >= 0 &&
        Math.floor(rect.bottom) <= (window.innerHeight || document.documentElement.clientHeight) &&
        Math.floor(rect.right) <= (window.innerWidth || document.documentElement.clientWidth));
};

var isObjectInArray = function (array, item, ignore) {
    if (ignore === void 0) { ignore = []; }
    return array.some(function (_item) {
        var result = true;
        for (var key in item) {
            if (!ignore.includes(key) && item[key] !== _item[key]) {
                result = false;
                break;
            }
        }
        return result;
    });
};

var usePopper = function () {
    var _popper = React$1.useRef();
    var el = React$1.useRef();
    var initPopper = function (reference, popper, options) {
        _popper.current = createPopper(reference, popper, options);
        el.current = popper;
    };
    var destroyPopper = function () {
        var popperInstance = _popper.current;
        if (popperInstance && el.current) {
            executeAfterTransition(function () {
                popperInstance.destroy();
            }, el.current);
        }
        _popper.current = undefined;
    };
    return {
        popper: _popper.current,
        initPopper: initPopper,
        destroyPopper: destroyPopper,
    };
};

var useStateWithCallback = function (initialState, handler, runHandler) {
    var _a = React$1.useState(initialState), state = _a[0], setState = _a[1];
    handler &&
        React$1.useEffect(function () {
            runHandler && handler(state);
        }, [state]);
    return [state, setState];
};

var CCollapse = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, horizontal = _a.horizontal, onHide = _a.onHide, onShow = _a.onShow, visible = _a.visible, rest = __rest$1(_a, ["children", "className", "horizontal", "onHide", "onShow", "visible"]);
    var collapseRef = React$1.useRef(null);
    var forkedRef = useForkedRef(ref, collapseRef);
    var _b = React$1.useState(), height = _b[0], setHeight = _b[1];
    var _c = React$1.useState(), width = _c[0], setWidth = _c[1];
    var onEntering = function () {
        onShow && onShow();
        if (horizontal) {
            collapseRef.current && setWidth(collapseRef.current.scrollWidth);
            return;
        }
        collapseRef.current && setHeight(collapseRef.current.scrollHeight);
    };
    var onEntered = function () {
        if (horizontal) {
            setWidth(0);
            return;
        }
        setHeight(0);
    };
    var onExit = function () {
        if (horizontal) {
            collapseRef.current && setWidth(collapseRef.current.scrollWidth);
            return;
        }
        collapseRef.current && setHeight(collapseRef.current.scrollHeight);
    };
    var onExiting = function () {
        onHide && onHide();
        if (horizontal) {
            setWidth(0);
            return;
        }
        setHeight(0);
    };
    var onExited = function () {
        if (horizontal) {
            setWidth(0);
            return;
        }
        setHeight(0);
    };
    return (React$1.createElement(CSSTransition$1, { in: visible, nodeRef: collapseRef, onEntering: onEntering, onEntered: onEntered, onExit: onExit, onExiting: onExiting, onExited: onExited, timeout: 350 }, function (state) {
        var currentHeight = height === 0 ? null : { height: height };
        var currentWidth = width === 0 ? null : { width: width };
        return (React$1.createElement("div", __assign$1({ className: classNames$1(className, {
                'collapse-horizontal': horizontal,
                collapsing: state === 'entering' || state === 'exiting',
                'collapse show': state === 'entered',
                collapse: state === 'exited',
            }), style: __assign$1(__assign$1({}, currentHeight), currentWidth) }, rest, { ref: forkedRef }), children));
    }));
});
CCollapse.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    horizontal: PropTypes$1.bool,
    onHide: PropTypes$1.func,
    onShow: PropTypes$1.func,
    visible: PropTypes$1.bool,
};
CCollapse.displayName = 'CCollapse';

var CAccordionBody = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, rest = __rest$1(_a, ["children", "className"]);
    var visible = React$1.useContext(CAccordionItemContext).visible;
    return (React$1.createElement(CCollapse, { className: "accordion-collapse", visible: visible },
        React$1.createElement("div", __assign$1({ className: classNames$1('accordion-body', className) }, rest, { ref: ref }), children)));
});
CAccordionBody.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
};
CAccordionBody.displayName = 'CAccordionBody';

var CAccordionButton = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, rest = __rest$1(_a, ["children", "className"]);
    var _b = React$1.useContext(CAccordionItemContext), visible = _b.visible, setVisible = _b.setVisible;
    return (React$1.createElement("button", __assign$1({ type: "button", className: classNames$1('accordion-button', { collapsed: !visible }, className), "aria-expanded": !visible, onClick: function () { return setVisible(!visible); } }, rest, { ref: ref }), children));
});
CAccordionButton.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
};
CAccordionButton.displayName = 'CAccordionButton';

var CAccordionHeader = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, rest = __rest$1(_a, ["children", "className"]);
    return (React$1.createElement("div", __assign$1({ className: classNames$1('accordion-header', className) }, rest, { ref: ref }),
        React$1.createElement(CAccordionButton, null, children)));
});
CAccordionHeader.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
};
CAccordionHeader.displayName = 'CAccordionHeader';

var CCloseButton = React$1.forwardRef(function (_a, ref) {
    var className = _a.className, disabled = _a.disabled, white = _a.white, rest = __rest$1(_a, ["className", "disabled", "white"]);
    return (React$1.createElement("button", __assign$1({ type: "button", className: classNames$1('btn', 'btn-close', {
            'btn-close-white': white,
        }, disabled, className), "aria-label": "Close", disabled: disabled }, rest, { ref: ref })));
});
CCloseButton.propTypes = {
    className: PropTypes$1.string,
    disabled: PropTypes$1.bool,
    white: PropTypes$1.bool,
};
CCloseButton.displayName = 'CCloseButton';

var colorPropType = PropTypes$1.oneOfType([
    PropTypes$1.oneOf([
        'primary',
        'secondary',
        'success',
        'danger',
        'warning',
        'info',
        'dark',
        'light',
    ]),
    PropTypes$1.string,
]);
var fallbackPlacementsPropType = PropTypes$1.oneOfType([
    PropTypes$1.arrayOf(PropTypes$1.oneOf(['top', 'bottom', 'right', 'left']).isRequired),
    PropTypes$1.oneOf(['top', 'bottom', 'right', 'left']),
]);
var gradientsPropType = PropTypes$1.oneOf([
    'primary-gradient',
    'secondary-gradient',
    'success-gradient',
    'danger-gradient',
    'warning-gradient',
    'info-gradient',
    'dark-gradient',
    'light-gradient',
]);
var placementPropType = PropTypes$1.oneOf([
    'auto',
    'auto-start',
    'auto-end',
    'top-end',
    'top',
    'top-start',
    'bottom-end',
    'bottom',
    'bottom-start',
    'right-start',
    'right',
    'right-end',
    'left-start',
    'left',
    'left-end',
]);
var shapePropType = PropTypes$1.oneOfType([
    PropTypes$1.oneOf([
        'rounded',
        'rounded-top',
        'rounded-end',
        'rounded-bottom',
        'rounded-start',
        'rounded-circle',
        'rounded-pill',
        'rounded-0',
        'rounded-1',
        'rounded-2',
        'rounded-3',
    ]),
    PropTypes$1.string,
]);
var textColorsPropType = PropTypes$1.oneOfType([
    colorPropType,
    PropTypes$1.oneOf(['white', 'muted']),
    PropTypes$1.string,
]);
var triggerPropType = PropTypes$1.oneOfType([
    PropTypes$1.arrayOf(PropTypes$1.oneOf(['hover', 'focus', 'click']).isRequired),
    PropTypes$1.oneOf(['hover', 'focus', 'click']),
]);

var CAlert = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, _b = _a.color, color = _b === void 0 ? 'primary' : _b, dismissible = _a.dismissible, variant = _a.variant, _c = _a.visible, visible = _c === void 0 ? true : _c, onClose = _a.onClose, rest = __rest$1(_a, ["children", "className", "color", "dismissible", "variant", "visible", "onClose"]);
    var alertRef = React$1.useRef(null);
    var forkedRef = useForkedRef(ref, alertRef);
    var _d = React$1.useState(visible), _visible = _d[0], setVisible = _d[1];
    React$1.useEffect(function () {
        setVisible(visible);
    }, [visible]);
    return (React$1.createElement(Transition$1, { in: _visible, mountOnEnter: true, nodeRef: alertRef, onExit: onClose, timeout: 150, unmountOnExit: true }, function (state) { return (React$1.createElement("div", __assign$1({ className: classNames$1('alert', variant === 'solid' ? "bg-".concat(color, " text-white") : "alert-".concat(color), {
            'alert-dismissible fade': dismissible,
            show: state === 'entered',
        }, className), role: "alert" }, rest, { ref: forkedRef }),
        children,
        dismissible && React$1.createElement(CCloseButton, { onClick: function () { return setVisible(false); } }))); }));
});
CAlert.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    color: colorPropType.isRequired,
    dismissible: PropTypes$1.bool,
    onClose: PropTypes$1.func,
    variant: PropTypes$1.string,
    visible: PropTypes$1.bool,
};
CAlert.displayName = 'CAlert';

var CAlertHeading = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, _b = _a.component, Component = _b === void 0 ? 'h4' : _b, rest = __rest$1(_a, ["children", "className", "component"]);
    return (React$1.createElement(Component, __assign$1({ className: classNames$1('alert-heading', className) }, rest, { ref: ref }), children));
});
CAlertHeading.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    component: PropTypes$1.elementType,
};
CAlertHeading.displayName = 'CAlertHeading';

var CLink = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, active = _a.active, className = _a.className, _b = _a.component, Component = _b === void 0 ? 'a' : _b, disabled = _a.disabled, rest = __rest$1(_a, ["children", "active", "className", "component", "disabled"]);
    return (React$1.createElement(Component
    // TODO: remove duplicated classes ex. `active active` in `<CListGroupItem>`
    , __assign$1({ 
        // TODO: remove duplicated classes ex. `active active` in `<CListGroupItem>`
        className: classNames$1(className, { active: active, disabled: disabled }) }, (active && { 'aria-current': 'page' }), (Component === 'a' && disabled && { 'aria-disabled': true, tabIndex: -1 }), ((Component === 'a' || Component === 'button') && {
        onClick: function (event) {
            event.preventDefault;
            !disabled && rest.onClick && rest.onClick(event);
        },
    }), { disabled: disabled }, rest, { ref: ref }), children));
});
CLink.propTypes = {
    active: PropTypes$1.bool,
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    component: PropTypes$1.elementType,
    disabled: PropTypes$1.bool,
};
CLink.displayName = 'CLink';

var CAlertLink = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, rest = __rest$1(_a, ["children", "className"]);
    return (React$1.createElement(CLink, __assign$1({ className: classNames$1('alert-link', className) }, rest, { ref: ref }), children));
});
CAlertLink.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
};
CAlertLink.displayName = 'CAlertLink';

var CAvatar = React$1.forwardRef(function (_a, ref) {
    var _b;
    var children = _a.children, className = _a.className, color = _a.color, shape = _a.shape, size = _a.size, src = _a.src, status = _a.status, textColor = _a.textColor, rest = __rest$1(_a, ["children", "className", "color", "shape", "size", "src", "status", "textColor"]);
    var statusClassName = status && classNames$1('avatar-status', "bg-".concat(status));
    return (React$1.createElement("div", __assign$1({ className: classNames$1('avatar', (_b = {},
            _b["bg-".concat(color)] = color,
            _b["avatar-".concat(size)] = size,
            _b["text-".concat(textColor)] = textColor,
            _b), shape, className) }, rest, { ref: ref }),
        src ? React$1.createElement("img", { src: src, className: "avatar-img" }) : children,
        status && React$1.createElement("span", { className: statusClassName })));
});
CAvatar.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    color: colorPropType,
    shape: shapePropType,
    size: PropTypes$1.string,
    src: PropTypes$1.string,
    status: PropTypes$1.string,
    textColor: textColorsPropType,
};
CAvatar.displayName = 'CAvatar';

var CBackdrop = React$1.forwardRef(function (_a, ref) {
    var _b = _a.className, className = _b === void 0 ? 'modal-backdrop' : _b, visible = _a.visible, rest = __rest$1(_a, ["className", "visible"]);
    var backdropRef = React$1.useRef(null);
    var forkedRef = useForkedRef(ref, backdropRef);
    return (React$1.createElement(Transition$1, { in: visible, mountOnEnter: true, nodeRef: backdropRef, timeout: 150, unmountOnExit: true }, function (state) { return (React$1.createElement("div", __assign$1({ className: classNames$1(className, 'fade', {
            show: state === 'entered',
        }) }, rest, { ref: forkedRef }))); }));
});
CBackdrop.propTypes = {
    className: PropTypes$1.string,
    visible: PropTypes$1.bool,
};
CBackdrop.displayName = 'CBackdrop';

var CBadge = React$1.forwardRef(function (_a, ref) {
    var _b;
    var children = _a.children, className = _a.className, color = _a.color, _c = _a.component, Component = _c === void 0 ? 'span' : _c, position = _a.position, shape = _a.shape, size = _a.size, textColor = _a.textColor, rest = __rest$1(_a, ["children", "className", "color", "component", "position", "shape", "size", "textColor"]);
    return (React$1.createElement(Component, __assign$1({ className: classNames$1('badge', (_b = {},
            _b["bg-".concat(color)] = color,
            _b['position-absolute translate-middle'] = position,
            _b['top-0'] = position === null || position === void 0 ? void 0 : position.includes('top'),
            _b['top-100'] = position === null || position === void 0 ? void 0 : position.includes('bottom'),
            _b['start-100'] = position === null || position === void 0 ? void 0 : position.includes('end'),
            _b['start-0'] = position === null || position === void 0 ? void 0 : position.includes('start'),
            _b["badge-".concat(size)] = size,
            _b["text-".concat(textColor)] = textColor,
            _b), shape, className) }, rest, { ref: ref }), children));
});
CBadge.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    color: PropTypes$1.oneOfType([colorPropType, gradientsPropType]),
    component: PropTypes$1.string,
    position: PropTypes$1.oneOf(['top-start', 'top-end', 'bottom-end', 'bottom-start']),
    shape: shapePropType,
    size: PropTypes$1.oneOf(['sm']),
    textColor: textColorsPropType,
};
CBadge.displayName = 'CBadge';

var CBreadcrumb = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, rest = __rest$1(_a, ["children", "className"]);
    return (React$1.createElement("nav", { "aria-label": "breadcrumb" },
        React$1.createElement("ol", __assign$1({ className: classNames$1('breadcrumb', className) }, rest, { ref: ref }), children)));
});
CBreadcrumb.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
};
CBreadcrumb.displayName = 'CBreadcrumb';

var CBreadcrumbItem = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, active = _a.active, className = _a.className, href = _a.href, rest = __rest$1(_a, ["children", "active", "className", "href"]);
    return (React$1.createElement("li", __assign$1({ className: classNames$1('breadcrumb-item', {
            active: active,
        }, className) }, (active && { 'aria-current': 'page' }), rest, { ref: ref }), href ? React$1.createElement(CLink, { href: href }, children) : children));
});
CBreadcrumbItem.propTypes = {
    active: PropTypes$1.bool,
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    href: PropTypes$1.string,
};
CBreadcrumbItem.displayName = 'CBreadcrumbItem';

var CButton = React$1.forwardRef(function (_a, ref) {
    var _b;
    var children = _a.children, className = _a.className, _c = _a.color, color = _c === void 0 ? 'primary' : _c, _d = _a.component, component = _d === void 0 ? 'button' : _d, shape = _a.shape, size = _a.size, _e = _a.type, type = _e === void 0 ? 'button' : _e, variant = _a.variant, rest = __rest$1(_a, ["children", "className", "color", "component", "shape", "size", "type", "variant"]);
    return (React$1.createElement(CLink, __assign$1({ component: rest.href ? 'a' : component, type: type, className: classNames$1('btn', variant ? "btn-".concat(variant, "-").concat(color) : "btn-".concat(color), (_b = {}, _b["btn-".concat(size)] = size, _b), shape, className) }, rest, { ref: ref }), children));
});
CButton.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    color: colorPropType,
    component: PropTypes$1.elementType,
    shape: PropTypes$1.string,
    size: PropTypes$1.oneOf(['sm', 'lg']),
    type: PropTypes$1.oneOf(['button', 'submit', 'reset']),
    variant: PropTypes$1.oneOf(['outline', 'ghost']),
};
CButton.displayName = 'CButton';

var CButtonToolbar = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, rest = __rest$1(_a, ["children", "className"]);
    return (React$1.createElement("div", __assign$1({ className: classNames$1('btn-toolbar', className) }, rest, { ref: ref }), children));
});
CButtonToolbar.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
};
CButtonToolbar.displayName = 'CButtonToolbar';

var CButtonGroup = React$1.forwardRef(function (_a, ref) {
    var _b;
    var children = _a.children, className = _a.className, size = _a.size, vertical = _a.vertical, rest = __rest$1(_a, ["children", "className", "size", "vertical"]);
    return (React$1.createElement("div", __assign$1({ className: classNames$1(vertical ? 'btn-group-vertical' : 'btn-group', (_b = {}, _b["btn-group-".concat(size)] = size, _b), className) }, rest, { ref: ref }), children));
});
CButtonGroup.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    size: PropTypes$1.oneOf(['sm', 'lg']),
    vertical: PropTypes$1.bool,
};
CButtonGroup.displayName = 'CButtonGroup';

var CCallout = React$1.forwardRef(function (_a, ref) {
    var _b;
    var children = _a.children, className = _a.className, color = _a.color, rest = __rest$1(_a, ["children", "className", "color"]);
    return (React$1.createElement("div", __assign$1({ className: classNames$1('callout', (_b = {},
            _b["callout-".concat(color)] = color,
            _b), className) }, rest, { ref: ref }), children));
});
CCallout.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    color: colorPropType,
};
CCallout.displayName = 'CCallout';

var CCard = React$1.forwardRef(function (_a, ref) {
    var _b;
    var children = _a.children, className = _a.className, color = _a.color, textColor = _a.textColor, rest = __rest$1(_a, ["children", "className", "color", "textColor"]);
    return (React$1.createElement("div", __assign$1({ className: classNames$1('card', (_b = {},
            _b["bg-".concat(color)] = color,
            _b["text-".concat(textColor)] = textColor,
            _b), className) }, rest, { ref: ref }), children));
});
CCard.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    color: PropTypes$1.oneOfType([colorPropType, gradientsPropType]),
    textColor: PropTypes$1.string,
};
CCard.displayName = 'CCard';

var CCardBody = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, rest = __rest$1(_a, ["children", "className"]);
    return (React$1.createElement("div", __assign$1({ className: classNames$1('card-body', className) }, rest, { ref: ref }), children));
});
CCardBody.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
};
CCardBody.displayName = 'CCardBody';

var CCardFooter = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, rest = __rest$1(_a, ["children", "className"]);
    return (React$1.createElement("div", __assign$1({ className: classNames$1('card-footer', className) }, rest, { ref: ref }), children));
});
CCardFooter.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
};
CCardFooter.displayName = 'CCardFooter';

var CCardGroup = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, rest = __rest$1(_a, ["children", "className"]);
    return (React$1.createElement("div", __assign$1({ className: classNames$1('card-group', className) }, rest, { ref: ref }), children));
});
CCardGroup.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
};
CCardGroup.displayName = 'CCardGroup';

var CCardHeader = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, _b = _a.component, Component = _b === void 0 ? 'div' : _b, className = _a.className, rest = __rest$1(_a, ["children", "component", "className"]);
    return (React$1.createElement(Component, __assign$1({ className: classNames$1('card-header', className) }, rest, { ref: ref }), children));
});
CCardHeader.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    component: PropTypes$1.elementType,
};
CCardHeader.displayName = 'CCardHeader';

var CCardImage = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, _b = _a.component, Component = _b === void 0 ? 'img' : _b, orientation = _a.orientation, rest = __rest$1(_a, ["children", "className", "component", "orientation"]);
    return (React$1.createElement(Component, __assign$1({ className: classNames$1(orientation ? "card-img-".concat(orientation) : 'card-img', className) }, rest, { ref: ref }), children));
});
CCardImage.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    component: PropTypes$1.elementType,
    orientation: PropTypes$1.oneOf(['top', 'bottom']),
};
CCardImage.displayName = 'CCardImage';

var CCardImageOverlay = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, rest = __rest$1(_a, ["children", "className"]);
    return (React$1.createElement("div", __assign$1({ className: classNames$1('card-img-overlay', className) }, rest, { ref: ref }), children));
});
CCardImageOverlay.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
};
CCardImageOverlay.displayName = 'CCardImageOverlay';

var CCardLink = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, rest = __rest$1(_a, ["children", "className"]);
    return (React$1.createElement(CLink, __assign$1({ className: classNames$1('card-link', className) }, rest, { ref: ref }), children));
});
CCardLink.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
};
CCardLink.displayName = 'CCardLink';

var CCardSubtitle = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, _b = _a.component, Component = _b === void 0 ? 'h6' : _b, className = _a.className, rest = __rest$1(_a, ["children", "component", "className"]);
    return (React$1.createElement(Component, __assign$1({ className: classNames$1('card-subtitle', className) }, rest, { ref: ref }), children));
});
CCardSubtitle.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    component: PropTypes$1.elementType,
};
CCardSubtitle.displayName = 'CCardSubtitle';

var CCardText = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, _b = _a.component, Component = _b === void 0 ? 'p' : _b, className = _a.className, rest = __rest$1(_a, ["children", "component", "className"]);
    return (React$1.createElement(Component, __assign$1({ className: classNames$1('card-text', className) }, rest, { ref: ref }), children));
});
CCardText.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    component: PropTypes$1.elementType,
};
CCardText.displayName = 'CCardText';

var CCardTitle = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, _b = _a.component, Component = _b === void 0 ? 'h5' : _b, className = _a.className, rest = __rest$1(_a, ["children", "component", "className"]);
    return (React$1.createElement(Component, __assign$1({ className: classNames$1('card-title', className) }, rest, { ref: ref }), children));
});
CCardTitle.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    component: PropTypes$1.elementType,
};
CCardTitle.displayName = 'CCardTitle';

var CCarouselContext = React$1.createContext({});
var CCarousel = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, _b = _a.activeIndex, activeIndex = _b === void 0 ? 0 : _b, className = _a.className, controls = _a.controls, dark = _a.dark, indicators = _a.indicators, _c = _a.interval, interval = _c === void 0 ? 5000 : _c, onSlid = _a.onSlid, onSlide = _a.onSlide, _d = _a.pause, pause = _d === void 0 ? 'hover' : _d, _e = _a.touch, touch = _e === void 0 ? true : _e, transition = _a.transition, _f = _a.wrap, wrap = _f === void 0 ? true : _f, rest = __rest$1(_a, ["children", "activeIndex", "className", "controls", "dark", "indicators", "interval", "onSlid", "onSlide", "pause", "touch", "transition", "wrap"]);
    var carouselRef = React$1.useRef(null);
    var forkedRef = useForkedRef(ref, carouselRef);
    var data = React$1.useRef({}).current;
    var _g = React$1.useState(activeIndex), active = _g[0], setActive = _g[1];
    var _h = React$1.useState(false), animating = _h[0], setAnimating = _h[1];
    var _j = React$1.useState(), customInterval = _j[0], setCustomInterval = _j[1];
    var _k = React$1.useState('next'), direction = _k[0], setDirection = _k[1];
    var _l = React$1.useState(0), itemsNumber = _l[0], setItemsNumber = _l[1];
    var _m = React$1.useState(null), touchPosition = _m[0], setTouchPosition = _m[1];
    var _o = React$1.useState(), visible = _o[0], setVisible = _o[1];
    React$1.useEffect(function () {
        setItemsNumber(React$1.Children.toArray(children).length);
    });
    React$1.useEffect(function () {
        visible && cycle();
    }, [visible]);
    React$1.useEffect(function () {
        !animating && cycle();
        !animating && onSlid && onSlid(active, direction);
        animating && onSlide && onSlide(active, direction);
    }, [animating]);
    React$1.useEffect(function () {
        window.addEventListener('scroll', handleScroll);
        return function () {
            window.removeEventListener('scroll', handleScroll);
        };
    });
    var cycle = function () {
        _pause();
        if (!wrap && active === itemsNumber - 1) {
            return;
        }
        if (typeof interval === 'number') {
            data.timeout = setTimeout(function () { return nextItemWhenVisible(); }, typeof customInterval === 'number' ? customInterval : interval);
        }
    };
    var _pause = function () { return pause && data.timeout && clearTimeout(data.timeout); };
    var nextItemWhenVisible = function () {
        // Don't call next when the page isn't visible
        // or the carousel or its parent isn't visible
        if (!document.hidden && carouselRef.current && isInViewport(carouselRef.current)) {
            if (animating) {
                return;
            }
            handleControlClick('next');
        }
    };
    var handleControlClick = function (direction) {
        if (animating) {
            return;
        }
        setDirection(direction);
        if (direction === 'next') {
            active === itemsNumber - 1 ? setActive(0) : setActive(active + 1);
        }
        else {
            active === 0 ? setActive(itemsNumber - 1) : setActive(active - 1);
        }
    };
    var handleIndicatorClick = function (index) {
        if (active === index) {
            return;
        }
        if (active < index) {
            setDirection('next');
            setActive(index);
            return;
        }
        if (active > index) {
            setDirection('prev');
            setActive(index);
        }
    };
    var handleScroll = function () {
        if (!document.hidden && carouselRef.current && isInViewport(carouselRef.current)) {
            setVisible(true);
        }
        else {
            setVisible(false);
        }
    };
    var handleTouchMove = function (e) {
        var touchDown = touchPosition;
        if (touchDown === null) {
            return;
        }
        var currentTouch = e.touches[0].clientX;
        var diff = touchDown - currentTouch;
        if (diff > 5) {
            handleControlClick('next');
        }
        if (diff < -5) {
            handleControlClick('prev');
        }
        setTouchPosition(null);
    };
    var handleTouchStart = function (e) {
        var touchDown = e.touches[0].clientX;
        setTouchPosition(touchDown);
    };
    return (React$1.createElement("div", __assign$1({ className: classNames$1('carousel slide', {
            'carousel-dark': dark,
            'carousel-fade': transition === 'crossfade',
        }, className), onMouseEnter: _pause, onMouseLeave: cycle }, (touch && { onTouchStart: handleTouchStart, onTouchMove: handleTouchMove }), rest, { ref: forkedRef }),
        React$1.createElement(CCarouselContext.Provider, { value: {
                setAnimating: setAnimating,
                setCustomInterval: setCustomInterval,
            } },
            indicators && (React$1.createElement("ol", { className: "carousel-indicators" }, Array.from({ length: itemsNumber }, function (_, i) { return i; }).map(function (index) {
                return (React$1.createElement("li", { key: "indicator".concat(index), onClick: function () {
                        !animating && handleIndicatorClick(index);
                    }, className: active === index ? 'active' : '', "data-coreui-target": "" }));
            }))),
            React$1.createElement("div", { className: "carousel-inner" }, React$1.Children.map(children, function (child, index) {
                if (React$1.isValidElement(child)) {
                    return React$1.cloneElement(child, {
                        active: active === index ? true : false,
                        direction: direction,
                        key: index,
                    });
                }
                return;
            })),
            controls && (React$1.createElement(React$1.Fragment, null,
                React$1.createElement("button", { className: "carousel-control-prev", onClick: function () { return handleControlClick('prev'); } },
                    React$1.createElement("span", { className: "carousel-control-prev-icon", "aria-label": "prev" })),
                React$1.createElement("button", { className: "carousel-control-next", onClick: function () { return handleControlClick('next'); } },
                    React$1.createElement("span", { className: "carousel-control-next-icon", "aria-label": "next" })))))));
});
CCarousel.propTypes = {
    activeIndex: PropTypes$1.number,
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    controls: PropTypes$1.bool,
    dark: PropTypes$1.bool,
    indicators: PropTypes$1.bool,
    interval: PropTypes$1.oneOfType([PropTypes$1.bool, PropTypes$1.number]),
    onSlid: PropTypes$1.func,
    onSlide: PropTypes$1.func,
    pause: PropTypes$1.oneOf([false, 'hover']),
    touch: PropTypes$1.bool,
    transition: PropTypes$1.oneOf(['slide', 'crossfade']),
    wrap: PropTypes$1.bool,
};
CCarousel.displayName = 'CCarousel';

var CCarouselCaption = React$1.forwardRef(function (_a, ref) {
    var className = _a.className, rest = __rest$1(_a, ["className"]);
    return React$1.createElement("div", __assign$1({ className: classNames$1('carousel-caption', className) }, rest, { ref: ref }));
});
CCarouselCaption.propTypes = {
    className: PropTypes$1.string,
};
CCarouselCaption.displayName = 'CCarouselCaption';

var CCarouselItem = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, active = _a.active, direction = _a.direction, _b = _a.interval, interval = _b === void 0 ? false : _b, rest = __rest$1(_a, ["children", "className", "active", "direction", "interval"]);
    var _c = React$1.useContext(CCarouselContext), setAnimating = _c.setAnimating, setCustomInterval = _c.setCustomInterval;
    var carouselItemRef = React$1.useRef(null);
    var forkedRef = useForkedRef(ref, carouselItemRef);
    var prevActive = React$1.useRef();
    var _d = React$1.useState(), directionClassName = _d[0], setDirectionClassName = _d[1];
    var _e = React$1.useState(), orderClassName = _e[0], setOrderClassName = _e[1];
    var _f = React$1.useState(active && 'active'), activeClassName = _f[0], setActiveClassName = _f[1];
    var _g = React$1.useState(0), count = _g[0], setCount = _g[1];
    React$1.useEffect(function () {
        if (active) {
            setCustomInterval(interval);
            if (count !== 0)
                setOrderClassName("carousel-item-".concat(direction));
        }
        if (prevActive.current && !active) {
            setActiveClassName('active');
        }
        if (active || prevActive.current) {
            setTimeout(function () {
                var _a;
                if (count !== 0) {
                    // @ts-expect-error reflow is necessary to proper transition
                    // eslint-disable-next-line @typescript-eslint/no-unused-vars
                    (_a = carouselItemRef.current) === null || _a === void 0 ? void 0 : _a.offsetHeight;
                    setDirectionClassName("carousel-item-".concat(direction === 'next' ? 'start' : 'end'));
                }
            }, 0);
        }
        prevActive.current = active;
        if (count === 0)
            setCount(count + 1);
    }, [active]);
    React$1.useEffect(function () {
        var _a, _b;
        (_a = carouselItemRef.current) === null || _a === void 0 ? void 0 : _a.addEventListener('transitionstart', function () {
            active && setAnimating(true);
        });
        (_b = carouselItemRef.current) === null || _b === void 0 ? void 0 : _b.addEventListener('transitionend', function () {
            active && setAnimating(false);
            setDirectionClassName('');
            setOrderClassName('');
            if (active) {
                setActiveClassName('active');
            }
            if (!active) {
                setActiveClassName('');
            }
        });
        return function () {
            var _a, _b;
            (_a = carouselItemRef.current) === null || _a === void 0 ? void 0 : _a.removeEventListener('transitionstart', function () {
                active && setAnimating(true);
            });
            (_b = carouselItemRef.current) === null || _b === void 0 ? void 0 : _b.removeEventListener('transitionend', function () {
                active && setAnimating(false);
                setDirectionClassName('');
                setOrderClassName('');
                if (active) {
                    setActiveClassName('active');
                }
                if (!active) {
                    setActiveClassName('');
                }
            });
        };
    });
    return (React$1.createElement("div", __assign$1({ className: classNames$1('carousel-item', activeClassName, directionClassName, orderClassName, className), ref: forkedRef }, rest), children));
});
CCarouselItem.propTypes = {
    active: PropTypes$1.bool,
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    direction: PropTypes$1.string,
    interval: PropTypes$1.oneOfType([PropTypes$1.bool, PropTypes$1.number]),
};
CCarouselItem.displayName = 'CCarouselItem';

var getContainer = function (container) {
    if (container) {
        return typeof container === 'function' ? container() : container;
    }
    return document.body;
};
var CConditionalPortal = function (_a) {
    var children = _a.children, container = _a.container, portal = _a.portal;
    var _b = React$1.useState(null), _container = _b[0], setContainer = _b[1];
    React$1.useEffect(function () {
        portal && setContainer(getContainer(container) || document.body);
    }, [container, portal]);
    return typeof window !== 'undefined' && portal && _container ? (ReactDOM.createPortal(children, _container)) : (React$1.createElement(React$1.Fragment, null, children));
};
CConditionalPortal.propTypes = {
    children: PropTypes$1.node,
    container: PropTypes$1.any,
    portal: PropTypes$1.bool,
};
CConditionalPortal.displayName = 'CConditionalPortal';

function _typeof$1(obj) {
  "@babel/helpers - typeof";

  return _typeof$1 = "function" == typeof Symbol && "symbol" == typeof Symbol.iterator ? function (obj) {
    return typeof obj;
  } : function (obj) {
    return obj && "function" == typeof Symbol && obj.constructor === Symbol && obj !== Symbol.prototype ? "symbol" : typeof obj;
  }, _typeof$1(obj);
}

function toInteger(dirtyNumber) {
  if (dirtyNumber === null || dirtyNumber === true || dirtyNumber === false) {
    return NaN;
  }
  var number = Number(dirtyNumber);
  if (isNaN(number)) {
    return number;
  }
  return number < 0 ? Math.ceil(number) : Math.floor(number);
}

function requiredArgs(required, args) {
  if (args.length < required) {
    throw new TypeError(required + ' argument' + (required > 1 ? 's' : '') + ' required, but only ' + args.length + ' present');
  }
}

/**
 * @name toDate
 * @category Common Helpers
 * @summary Convert the given argument to an instance of Date.
 *
 * @description
 * Convert the given argument to an instance of Date.
 *
 * If the argument is an instance of Date, the function returns its clone.
 *
 * If the argument is a number, it is treated as a timestamp.
 *
 * If the argument is none of the above, the function returns Invalid Date.
 *
 * **Note**: *all* Date arguments passed to any *date-fns* function is processed by `toDate`.
 *
 * @param {Date|Number} argument - the value to convert
 * @returns {Date} the parsed date in the local time zone
 * @throws {TypeError} 1 argument required
 *
 * @example
 * // Clone the date:
 * const result = toDate(new Date(2014, 1, 11, 11, 30, 30))
 * //=> Tue Feb 11 2014 11:30:30
 *
 * @example
 * // Convert the timestamp to date:
 * const result = toDate(1392098430000)
 * //=> Tue Feb 11 2014 11:30:30
 */
function toDate(argument) {
  requiredArgs(1, arguments);
  var argStr = Object.prototype.toString.call(argument);

  // Clone the date
  if (argument instanceof Date || _typeof$1(argument) === 'object' && argStr === '[object Date]') {
    // Prevent the date to lose the milliseconds when passed to new Date() in IE10
    return new Date(argument.getTime());
  } else if (typeof argument === 'number' || argStr === '[object Number]') {
    return new Date(argument);
  } else {
    if ((typeof argument === 'string' || argStr === '[object String]') && typeof console !== 'undefined') {
      // eslint-disable-next-line no-console
      console.warn("Starting with v2.0.0-beta.1 date-fns doesn't accept strings as date arguments. Please use `parseISO` to parse strings. See: https://github.com/date-fns/date-fns/blob/master/docs/upgradeGuide.md#string-arguments");
      // eslint-disable-next-line no-console
      console.warn(new Error().stack);
    }
    return new Date(NaN);
  }
}

/**
 * @name addMilliseconds
 * @category Millisecond Helpers
 * @summary Add the specified number of milliseconds to the given date.
 *
 * @description
 * Add the specified number of milliseconds to the given date.
 *
 * @param {Date|Number} date - the date to be changed
 * @param {Number} amount - the amount of milliseconds to be added. Positive decimals will be rounded using `Math.floor`, decimals less than zero will be rounded using `Math.ceil`.
 * @returns {Date} the new date with the milliseconds added
 * @throws {TypeError} 2 arguments required
 *
 * @example
 * // Add 750 milliseconds to 10 July 2014 12:45:30.000:
 * const result = addMilliseconds(new Date(2014, 6, 10, 12, 45, 30, 0), 750)
 * //=> Thu Jul 10 2014 12:45:30.750
 */
function addMilliseconds(dirtyDate, dirtyAmount) {
  requiredArgs(2, arguments);
  var timestamp = toDate(dirtyDate).getTime();
  var amount = toInteger(dirtyAmount);
  return new Date(timestamp + amount);
}

var defaultOptions = {};
function getDefaultOptions() {
  return defaultOptions;
}

/**
 * Google Chrome as of 67.0.3396.87 introduced timezones with offset that includes seconds.
 * They usually appear for dates that denote time before the timezones were introduced
 * (e.g. for 'Europe/Prague' timezone the offset is GMT+00:57:44 before 1 October 1891
 * and GMT+01:00:00 after that date)
 *
 * Date#getTimezoneOffset returns the offset in minutes and would return 57 for the example above,
 * which would lead to incorrect calculations.
 *
 * This function returns the timezone offset in milliseconds that takes seconds in account.
 */
function getTimezoneOffsetInMilliseconds(date) {
  var utcDate = new Date(Date.UTC(date.getFullYear(), date.getMonth(), date.getDate(), date.getHours(), date.getMinutes(), date.getSeconds(), date.getMilliseconds()));
  utcDate.setUTCFullYear(date.getFullYear());
  return date.getTime() - utcDate.getTime();
}

/**
 * @name isDate
 * @category Common Helpers
 * @summary Is the given value a date?
 *
 * @description
 * Returns true if the given value is an instance of Date. The function works for dates transferred across iframes.
 *
 * @param {*} value - the value to check
 * @returns {boolean} true if the given value is a date
 * @throws {TypeError} 1 arguments required
 *
 * @example
 * // For a valid date:
 * const result = isDate(new Date())
 * //=> true
 *
 * @example
 * // For an invalid date:
 * const result = isDate(new Date(NaN))
 * //=> true
 *
 * @example
 * // For some value:
 * const result = isDate('2014-02-31')
 * //=> false
 *
 * @example
 * // For an object:
 * const result = isDate({})
 * //=> false
 */
function isDate(value) {
  requiredArgs(1, arguments);
  return value instanceof Date || _typeof$1(value) === 'object' && Object.prototype.toString.call(value) === '[object Date]';
}

/**
 * @name isValid
 * @category Common Helpers
 * @summary Is the given date valid?
 *
 * @description
 * Returns false if argument is Invalid Date and true otherwise.
 * Argument is converted to Date using `toDate`. See [toDate]{@link https://date-fns.org/docs/toDate}
 * Invalid Date is a Date, whose time value is NaN.
 *
 * Time value of Date: http://es5.github.io/#x15.9.1.1
 *
 * @param {*} date - the date to check
 * @returns {Boolean} the date is valid
 * @throws {TypeError} 1 argument required
 *
 * @example
 * // For the valid date:
 * const result = isValid(new Date(2014, 1, 31))
 * //=> true
 *
 * @example
 * // For the value, convertable into a date:
 * const result = isValid(1393804800000)
 * //=> true
 *
 * @example
 * // For the invalid date:
 * const result = isValid(new Date(''))
 * //=> false
 */
function isValid(dirtyDate) {
  requiredArgs(1, arguments);
  if (!isDate(dirtyDate) && typeof dirtyDate !== 'number') {
    return false;
  }
  var date = toDate(dirtyDate);
  return !isNaN(Number(date));
}

/**
 * @name subMilliseconds
 * @category Millisecond Helpers
 * @summary Subtract the specified number of milliseconds from the given date.
 *
 * @description
 * Subtract the specified number of milliseconds from the given date.
 *
 * @param {Date|Number} date - the date to be changed
 * @param {Number} amount - the amount of milliseconds to be subtracted. Positive decimals will be rounded using `Math.floor`, decimals less than zero will be rounded using `Math.ceil`.
 * @returns {Date} the new date with the milliseconds subtracted
 * @throws {TypeError} 2 arguments required
 *
 * @example
 * // Subtract 750 milliseconds from 10 July 2014 12:45:30.000:
 * const result = subMilliseconds(new Date(2014, 6, 10, 12, 45, 30, 0), 750)
 * //=> Thu Jul 10 2014 12:45:29.250
 */
function subMilliseconds(dirtyDate, dirtyAmount) {
  requiredArgs(2, arguments);
  var amount = toInteger(dirtyAmount);
  return addMilliseconds(dirtyDate, -amount);
}

var MILLISECONDS_IN_DAY = 86400000;
function getUTCDayOfYear(dirtyDate) {
  requiredArgs(1, arguments);
  var date = toDate(dirtyDate);
  var timestamp = date.getTime();
  date.setUTCMonth(0, 1);
  date.setUTCHours(0, 0, 0, 0);
  var startOfYearTimestamp = date.getTime();
  var difference = timestamp - startOfYearTimestamp;
  return Math.floor(difference / MILLISECONDS_IN_DAY) + 1;
}

function startOfUTCISOWeek(dirtyDate) {
  requiredArgs(1, arguments);
  var weekStartsOn = 1;
  var date = toDate(dirtyDate);
  var day = date.getUTCDay();
  var diff = (day < weekStartsOn ? 7 : 0) + day - weekStartsOn;
  date.setUTCDate(date.getUTCDate() - diff);
  date.setUTCHours(0, 0, 0, 0);
  return date;
}

function getUTCISOWeekYear(dirtyDate) {
  requiredArgs(1, arguments);
  var date = toDate(dirtyDate);
  var year = date.getUTCFullYear();
  var fourthOfJanuaryOfNextYear = new Date(0);
  fourthOfJanuaryOfNextYear.setUTCFullYear(year + 1, 0, 4);
  fourthOfJanuaryOfNextYear.setUTCHours(0, 0, 0, 0);
  var startOfNextYear = startOfUTCISOWeek(fourthOfJanuaryOfNextYear);
  var fourthOfJanuaryOfThisYear = new Date(0);
  fourthOfJanuaryOfThisYear.setUTCFullYear(year, 0, 4);
  fourthOfJanuaryOfThisYear.setUTCHours(0, 0, 0, 0);
  var startOfThisYear = startOfUTCISOWeek(fourthOfJanuaryOfThisYear);
  if (date.getTime() >= startOfNextYear.getTime()) {
    return year + 1;
  } else if (date.getTime() >= startOfThisYear.getTime()) {
    return year;
  } else {
    return year - 1;
  }
}

function startOfUTCISOWeekYear(dirtyDate) {
  requiredArgs(1, arguments);
  var year = getUTCISOWeekYear(dirtyDate);
  var fourthOfJanuary = new Date(0);
  fourthOfJanuary.setUTCFullYear(year, 0, 4);
  fourthOfJanuary.setUTCHours(0, 0, 0, 0);
  var date = startOfUTCISOWeek(fourthOfJanuary);
  return date;
}

var MILLISECONDS_IN_WEEK$1 = 604800000;
function getUTCISOWeek(dirtyDate) {
  requiredArgs(1, arguments);
  var date = toDate(dirtyDate);
  var diff = startOfUTCISOWeek(date).getTime() - startOfUTCISOWeekYear(date).getTime();

  // Round the number of days to the nearest integer
  // because the number of milliseconds in a week is not constant
  // (e.g. it's different in the week of the daylight saving time clock shift)
  return Math.round(diff / MILLISECONDS_IN_WEEK$1) + 1;
}

function startOfUTCWeek(dirtyDate, options) {
  var _ref, _ref2, _ref3, _options$weekStartsOn, _options$locale, _options$locale$optio, _defaultOptions$local, _defaultOptions$local2;
  requiredArgs(1, arguments);
  var defaultOptions = getDefaultOptions();
  var weekStartsOn = toInteger((_ref = (_ref2 = (_ref3 = (_options$weekStartsOn = options === null || options === void 0 ? void 0 : options.weekStartsOn) !== null && _options$weekStartsOn !== void 0 ? _options$weekStartsOn : options === null || options === void 0 ? void 0 : (_options$locale = options.locale) === null || _options$locale === void 0 ? void 0 : (_options$locale$optio = _options$locale.options) === null || _options$locale$optio === void 0 ? void 0 : _options$locale$optio.weekStartsOn) !== null && _ref3 !== void 0 ? _ref3 : defaultOptions.weekStartsOn) !== null && _ref2 !== void 0 ? _ref2 : (_defaultOptions$local = defaultOptions.locale) === null || _defaultOptions$local === void 0 ? void 0 : (_defaultOptions$local2 = _defaultOptions$local.options) === null || _defaultOptions$local2 === void 0 ? void 0 : _defaultOptions$local2.weekStartsOn) !== null && _ref !== void 0 ? _ref : 0);

  // Test if weekStartsOn is between 0 and 6 _and_ is not NaN
  if (!(weekStartsOn >= 0 && weekStartsOn <= 6)) {
    throw new RangeError('weekStartsOn must be between 0 and 6 inclusively');
  }
  var date = toDate(dirtyDate);
  var day = date.getUTCDay();
  var diff = (day < weekStartsOn ? 7 : 0) + day - weekStartsOn;
  date.setUTCDate(date.getUTCDate() - diff);
  date.setUTCHours(0, 0, 0, 0);
  return date;
}

function getUTCWeekYear(dirtyDate, options) {
  var _ref, _ref2, _ref3, _options$firstWeekCon, _options$locale, _options$locale$optio, _defaultOptions$local, _defaultOptions$local2;
  requiredArgs(1, arguments);
  var date = toDate(dirtyDate);
  var year = date.getUTCFullYear();
  var defaultOptions = getDefaultOptions();
  var firstWeekContainsDate = toInteger((_ref = (_ref2 = (_ref3 = (_options$firstWeekCon = options === null || options === void 0 ? void 0 : options.firstWeekContainsDate) !== null && _options$firstWeekCon !== void 0 ? _options$firstWeekCon : options === null || options === void 0 ? void 0 : (_options$locale = options.locale) === null || _options$locale === void 0 ? void 0 : (_options$locale$optio = _options$locale.options) === null || _options$locale$optio === void 0 ? void 0 : _options$locale$optio.firstWeekContainsDate) !== null && _ref3 !== void 0 ? _ref3 : defaultOptions.firstWeekContainsDate) !== null && _ref2 !== void 0 ? _ref2 : (_defaultOptions$local = defaultOptions.locale) === null || _defaultOptions$local === void 0 ? void 0 : (_defaultOptions$local2 = _defaultOptions$local.options) === null || _defaultOptions$local2 === void 0 ? void 0 : _defaultOptions$local2.firstWeekContainsDate) !== null && _ref !== void 0 ? _ref : 1);

  // Test if weekStartsOn is between 1 and 7 _and_ is not NaN
  if (!(firstWeekContainsDate >= 1 && firstWeekContainsDate <= 7)) {
    throw new RangeError('firstWeekContainsDate must be between 1 and 7 inclusively');
  }
  var firstWeekOfNextYear = new Date(0);
  firstWeekOfNextYear.setUTCFullYear(year + 1, 0, firstWeekContainsDate);
  firstWeekOfNextYear.setUTCHours(0, 0, 0, 0);
  var startOfNextYear = startOfUTCWeek(firstWeekOfNextYear, options);
  var firstWeekOfThisYear = new Date(0);
  firstWeekOfThisYear.setUTCFullYear(year, 0, firstWeekContainsDate);
  firstWeekOfThisYear.setUTCHours(0, 0, 0, 0);
  var startOfThisYear = startOfUTCWeek(firstWeekOfThisYear, options);
  if (date.getTime() >= startOfNextYear.getTime()) {
    return year + 1;
  } else if (date.getTime() >= startOfThisYear.getTime()) {
    return year;
  } else {
    return year - 1;
  }
}

function startOfUTCWeekYear(dirtyDate, options) {
  var _ref, _ref2, _ref3, _options$firstWeekCon, _options$locale, _options$locale$optio, _defaultOptions$local, _defaultOptions$local2;
  requiredArgs(1, arguments);
  var defaultOptions = getDefaultOptions();
  var firstWeekContainsDate = toInteger((_ref = (_ref2 = (_ref3 = (_options$firstWeekCon = options === null || options === void 0 ? void 0 : options.firstWeekContainsDate) !== null && _options$firstWeekCon !== void 0 ? _options$firstWeekCon : options === null || options === void 0 ? void 0 : (_options$locale = options.locale) === null || _options$locale === void 0 ? void 0 : (_options$locale$optio = _options$locale.options) === null || _options$locale$optio === void 0 ? void 0 : _options$locale$optio.firstWeekContainsDate) !== null && _ref3 !== void 0 ? _ref3 : defaultOptions.firstWeekContainsDate) !== null && _ref2 !== void 0 ? _ref2 : (_defaultOptions$local = defaultOptions.locale) === null || _defaultOptions$local === void 0 ? void 0 : (_defaultOptions$local2 = _defaultOptions$local.options) === null || _defaultOptions$local2 === void 0 ? void 0 : _defaultOptions$local2.firstWeekContainsDate) !== null && _ref !== void 0 ? _ref : 1);
  var year = getUTCWeekYear(dirtyDate, options);
  var firstWeek = new Date(0);
  firstWeek.setUTCFullYear(year, 0, firstWeekContainsDate);
  firstWeek.setUTCHours(0, 0, 0, 0);
  var date = startOfUTCWeek(firstWeek, options);
  return date;
}

var MILLISECONDS_IN_WEEK = 604800000;
function getUTCWeek(dirtyDate, options) {
  requiredArgs(1, arguments);
  var date = toDate(dirtyDate);
  var diff = startOfUTCWeek(date, options).getTime() - startOfUTCWeekYear(date, options).getTime();

  // Round the number of days to the nearest integer
  // because the number of milliseconds in a week is not constant
  // (e.g. it's different in the week of the daylight saving time clock shift)
  return Math.round(diff / MILLISECONDS_IN_WEEK) + 1;
}

function addLeadingZeros(number, targetLength) {
  var sign = number < 0 ? '-' : '';
  var output = Math.abs(number).toString();
  while (output.length < targetLength) {
    output = '0' + output;
  }
  return sign + output;
}

/*
 * |     | Unit                           |     | Unit                           |
 * |-----|--------------------------------|-----|--------------------------------|
 * |  a  | AM, PM                         |  A* |                                |
 * |  d  | Day of month                   |  D  |                                |
 * |  h  | Hour [1-12]                    |  H  | Hour [0-23]                    |
 * |  m  | Minute                         |  M  | Month                          |
 * |  s  | Second                         |  S  | Fraction of second             |
 * |  y  | Year (abs)                     |  Y  |                                |
 *
 * Letters marked by * are not implemented but reserved by Unicode standard.
 */
var formatters$2 = {
  // Year
  y: function y(date, token) {
    // From http://www.unicode.org/reports/tr35/tr35-31/tr35-dates.html#Date_Format_tokens
    // | Year     |     y | yy |   yyy |  yyyy | yyyyy |
    // |----------|-------|----|-------|-------|-------|
    // | AD 1     |     1 | 01 |   001 |  0001 | 00001 |
    // | AD 12    |    12 | 12 |   012 |  0012 | 00012 |
    // | AD 123   |   123 | 23 |   123 |  0123 | 00123 |
    // | AD 1234  |  1234 | 34 |  1234 |  1234 | 01234 |
    // | AD 12345 | 12345 | 45 | 12345 | 12345 | 12345 |

    var signedYear = date.getUTCFullYear();
    // Returns 1 for 1 BC (which is year 0 in JavaScript)
    var year = signedYear > 0 ? signedYear : 1 - signedYear;
    return addLeadingZeros(token === 'yy' ? year % 100 : year, token.length);
  },
  // Month
  M: function M(date, token) {
    var month = date.getUTCMonth();
    return token === 'M' ? String(month + 1) : addLeadingZeros(month + 1, 2);
  },
  // Day of the month
  d: function d(date, token) {
    return addLeadingZeros(date.getUTCDate(), token.length);
  },
  // AM or PM
  a: function a(date, token) {
    var dayPeriodEnumValue = date.getUTCHours() / 12 >= 1 ? 'pm' : 'am';
    switch (token) {
      case 'a':
      case 'aa':
        return dayPeriodEnumValue.toUpperCase();
      case 'aaa':
        return dayPeriodEnumValue;
      case 'aaaaa':
        return dayPeriodEnumValue[0];
      case 'aaaa':
      default:
        return dayPeriodEnumValue === 'am' ? 'a.m.' : 'p.m.';
    }
  },
  // Hour [1-12]
  h: function h(date, token) {
    return addLeadingZeros(date.getUTCHours() % 12 || 12, token.length);
  },
  // Hour [0-23]
  H: function H(date, token) {
    return addLeadingZeros(date.getUTCHours(), token.length);
  },
  // Minute
  m: function m(date, token) {
    return addLeadingZeros(date.getUTCMinutes(), token.length);
  },
  // Second
  s: function s(date, token) {
    return addLeadingZeros(date.getUTCSeconds(), token.length);
  },
  // Fraction of second
  S: function S(date, token) {
    var numberOfDigits = token.length;
    var milliseconds = date.getUTCMilliseconds();
    var fractionalSeconds = Math.floor(milliseconds * Math.pow(10, numberOfDigits - 3));
    return addLeadingZeros(fractionalSeconds, token.length);
  }
};
var formatters$3 = formatters$2;

var dayPeriodEnum = {
  am: 'am',
  pm: 'pm',
  midnight: 'midnight',
  noon: 'noon',
  morning: 'morning',
  afternoon: 'afternoon',
  evening: 'evening',
  night: 'night'
};
/*
 * |     | Unit                           |     | Unit                           |
 * |-----|--------------------------------|-----|--------------------------------|
 * |  a  | AM, PM                         |  A* | Milliseconds in day            |
 * |  b  | AM, PM, noon, midnight         |  B  | Flexible day period            |
 * |  c  | Stand-alone local day of week  |  C* | Localized hour w/ day period   |
 * |  d  | Day of month                   |  D  | Day of year                    |
 * |  e  | Local day of week              |  E  | Day of week                    |
 * |  f  |                                |  F* | Day of week in month           |
 * |  g* | Modified Julian day            |  G  | Era                            |
 * |  h  | Hour [1-12]                    |  H  | Hour [0-23]                    |
 * |  i! | ISO day of week                |  I! | ISO week of year               |
 * |  j* | Localized hour w/ day period   |  J* | Localized hour w/o day period  |
 * |  k  | Hour [1-24]                    |  K  | Hour [0-11]                    |
 * |  l* | (deprecated)                   |  L  | Stand-alone month              |
 * |  m  | Minute                         |  M  | Month                          |
 * |  n  |                                |  N  |                                |
 * |  o! | Ordinal number modifier        |  O  | Timezone (GMT)                 |
 * |  p! | Long localized time            |  P! | Long localized date            |
 * |  q  | Stand-alone quarter            |  Q  | Quarter                        |
 * |  r* | Related Gregorian year         |  R! | ISO week-numbering year        |
 * |  s  | Second                         |  S  | Fraction of second             |
 * |  t! | Seconds timestamp              |  T! | Milliseconds timestamp         |
 * |  u  | Extended year                  |  U* | Cyclic year                    |
 * |  v* | Timezone (generic non-locat.)  |  V* | Timezone (location)            |
 * |  w  | Local week of year             |  W* | Week of month                  |
 * |  x  | Timezone (ISO-8601 w/o Z)      |  X  | Timezone (ISO-8601)            |
 * |  y  | Year (abs)                     |  Y  | Local week-numbering year      |
 * |  z  | Timezone (specific non-locat.) |  Z* | Timezone (aliases)             |
 *
 * Letters marked by * are not implemented but reserved by Unicode standard.
 *
 * Letters marked by ! are non-standard, but implemented by date-fns:
 * - `o` modifies the previous token to turn it into an ordinal (see `format` docs)
 * - `i` is ISO day of week. For `i` and `ii` is returns numeric ISO week days,
 *   i.e. 7 for Sunday, 1 for Monday, etc.
 * - `I` is ISO week of year, as opposed to `w` which is local week of year.
 * - `R` is ISO week-numbering year, as opposed to `Y` which is local week-numbering year.
 *   `R` is supposed to be used in conjunction with `I` and `i`
 *   for universal ISO week-numbering date, whereas
 *   `Y` is supposed to be used in conjunction with `w` and `e`
 *   for week-numbering date specific to the locale.
 * - `P` is long localized date format
 * - `p` is long localized time format
 */

var formatters = {
  // Era
  G: function G(date, token, localize) {
    var era = date.getUTCFullYear() > 0 ? 1 : 0;
    switch (token) {
      // AD, BC
      case 'G':
      case 'GG':
      case 'GGG':
        return localize.era(era, {
          width: 'abbreviated'
        });
      // A, B
      case 'GGGGG':
        return localize.era(era, {
          width: 'narrow'
        });
      // Anno Domini, Before Christ
      case 'GGGG':
      default:
        return localize.era(era, {
          width: 'wide'
        });
    }
  },
  // Year
  y: function y(date, token, localize) {
    // Ordinal number
    if (token === 'yo') {
      var signedYear = date.getUTCFullYear();
      // Returns 1 for 1 BC (which is year 0 in JavaScript)
      var year = signedYear > 0 ? signedYear : 1 - signedYear;
      return localize.ordinalNumber(year, {
        unit: 'year'
      });
    }
    return formatters$3.y(date, token);
  },
  // Local week-numbering year
  Y: function Y(date, token, localize, options) {
    var signedWeekYear = getUTCWeekYear(date, options);
    // Returns 1 for 1 BC (which is year 0 in JavaScript)
    var weekYear = signedWeekYear > 0 ? signedWeekYear : 1 - signedWeekYear;

    // Two digit year
    if (token === 'YY') {
      var twoDigitYear = weekYear % 100;
      return addLeadingZeros(twoDigitYear, 2);
    }

    // Ordinal number
    if (token === 'Yo') {
      return localize.ordinalNumber(weekYear, {
        unit: 'year'
      });
    }

    // Padding
    return addLeadingZeros(weekYear, token.length);
  },
  // ISO week-numbering year
  R: function R(date, token) {
    var isoWeekYear = getUTCISOWeekYear(date);

    // Padding
    return addLeadingZeros(isoWeekYear, token.length);
  },
  // Extended year. This is a single number designating the year of this calendar system.
  // The main difference between `y` and `u` localizers are B.C. years:
  // | Year | `y` | `u` |
  // |------|-----|-----|
  // | AC 1 |   1 |   1 |
  // | BC 1 |   1 |   0 |
  // | BC 2 |   2 |  -1 |
  // Also `yy` always returns the last two digits of a year,
  // while `uu` pads single digit years to 2 characters and returns other years unchanged.
  u: function u(date, token) {
    var year = date.getUTCFullYear();
    return addLeadingZeros(year, token.length);
  },
  // Quarter
  Q: function Q(date, token, localize) {
    var quarter = Math.ceil((date.getUTCMonth() + 1) / 3);
    switch (token) {
      // 1, 2, 3, 4
      case 'Q':
        return String(quarter);
      // 01, 02, 03, 04
      case 'QQ':
        return addLeadingZeros(quarter, 2);
      // 1st, 2nd, 3rd, 4th
      case 'Qo':
        return localize.ordinalNumber(quarter, {
          unit: 'quarter'
        });
      // Q1, Q2, Q3, Q4
      case 'QQQ':
        return localize.quarter(quarter, {
          width: 'abbreviated',
          context: 'formatting'
        });
      // 1, 2, 3, 4 (narrow quarter; could be not numerical)
      case 'QQQQQ':
        return localize.quarter(quarter, {
          width: 'narrow',
          context: 'formatting'
        });
      // 1st quarter, 2nd quarter, ...
      case 'QQQQ':
      default:
        return localize.quarter(quarter, {
          width: 'wide',
          context: 'formatting'
        });
    }
  },
  // Stand-alone quarter
  q: function q(date, token, localize) {
    var quarter = Math.ceil((date.getUTCMonth() + 1) / 3);
    switch (token) {
      // 1, 2, 3, 4
      case 'q':
        return String(quarter);
      // 01, 02, 03, 04
      case 'qq':
        return addLeadingZeros(quarter, 2);
      // 1st, 2nd, 3rd, 4th
      case 'qo':
        return localize.ordinalNumber(quarter, {
          unit: 'quarter'
        });
      // Q1, Q2, Q3, Q4
      case 'qqq':
        return localize.quarter(quarter, {
          width: 'abbreviated',
          context: 'standalone'
        });
      // 1, 2, 3, 4 (narrow quarter; could be not numerical)
      case 'qqqqq':
        return localize.quarter(quarter, {
          width: 'narrow',
          context: 'standalone'
        });
      // 1st quarter, 2nd quarter, ...
      case 'qqqq':
      default:
        return localize.quarter(quarter, {
          width: 'wide',
          context: 'standalone'
        });
    }
  },
  // Month
  M: function M(date, token, localize) {
    var month = date.getUTCMonth();
    switch (token) {
      case 'M':
      case 'MM':
        return formatters$3.M(date, token);
      // 1st, 2nd, ..., 12th
      case 'Mo':
        return localize.ordinalNumber(month + 1, {
          unit: 'month'
        });
      // Jan, Feb, ..., Dec
      case 'MMM':
        return localize.month(month, {
          width: 'abbreviated',
          context: 'formatting'
        });
      // J, F, ..., D
      case 'MMMMM':
        return localize.month(month, {
          width: 'narrow',
          context: 'formatting'
        });
      // January, February, ..., December
      case 'MMMM':
      default:
        return localize.month(month, {
          width: 'wide',
          context: 'formatting'
        });
    }
  },
  // Stand-alone month
  L: function L(date, token, localize) {
    var month = date.getUTCMonth();
    switch (token) {
      // 1, 2, ..., 12
      case 'L':
        return String(month + 1);
      // 01, 02, ..., 12
      case 'LL':
        return addLeadingZeros(month + 1, 2);
      // 1st, 2nd, ..., 12th
      case 'Lo':
        return localize.ordinalNumber(month + 1, {
          unit: 'month'
        });
      // Jan, Feb, ..., Dec
      case 'LLL':
        return localize.month(month, {
          width: 'abbreviated',
          context: 'standalone'
        });
      // J, F, ..., D
      case 'LLLLL':
        return localize.month(month, {
          width: 'narrow',
          context: 'standalone'
        });
      // January, February, ..., December
      case 'LLLL':
      default:
        return localize.month(month, {
          width: 'wide',
          context: 'standalone'
        });
    }
  },
  // Local week of year
  w: function w(date, token, localize, options) {
    var week = getUTCWeek(date, options);
    if (token === 'wo') {
      return localize.ordinalNumber(week, {
        unit: 'week'
      });
    }
    return addLeadingZeros(week, token.length);
  },
  // ISO week of year
  I: function I(date, token, localize) {
    var isoWeek = getUTCISOWeek(date);
    if (token === 'Io') {
      return localize.ordinalNumber(isoWeek, {
        unit: 'week'
      });
    }
    return addLeadingZeros(isoWeek, token.length);
  },
  // Day of the month
  d: function d(date, token, localize) {
    if (token === 'do') {
      return localize.ordinalNumber(date.getUTCDate(), {
        unit: 'date'
      });
    }
    return formatters$3.d(date, token);
  },
  // Day of year
  D: function D(date, token, localize) {
    var dayOfYear = getUTCDayOfYear(date);
    if (token === 'Do') {
      return localize.ordinalNumber(dayOfYear, {
        unit: 'dayOfYear'
      });
    }
    return addLeadingZeros(dayOfYear, token.length);
  },
  // Day of week
  E: function E(date, token, localize) {
    var dayOfWeek = date.getUTCDay();
    switch (token) {
      // Tue
      case 'E':
      case 'EE':
      case 'EEE':
        return localize.day(dayOfWeek, {
          width: 'abbreviated',
          context: 'formatting'
        });
      // T
      case 'EEEEE':
        return localize.day(dayOfWeek, {
          width: 'narrow',
          context: 'formatting'
        });
      // Tu
      case 'EEEEEE':
        return localize.day(dayOfWeek, {
          width: 'short',
          context: 'formatting'
        });
      // Tuesday
      case 'EEEE':
      default:
        return localize.day(dayOfWeek, {
          width: 'wide',
          context: 'formatting'
        });
    }
  },
  // Local day of week
  e: function e(date, token, localize, options) {
    var dayOfWeek = date.getUTCDay();
    var localDayOfWeek = (dayOfWeek - options.weekStartsOn + 8) % 7 || 7;
    switch (token) {
      // Numerical value (Nth day of week with current locale or weekStartsOn)
      case 'e':
        return String(localDayOfWeek);
      // Padded numerical value
      case 'ee':
        return addLeadingZeros(localDayOfWeek, 2);
      // 1st, 2nd, ..., 7th
      case 'eo':
        return localize.ordinalNumber(localDayOfWeek, {
          unit: 'day'
        });
      case 'eee':
        return localize.day(dayOfWeek, {
          width: 'abbreviated',
          context: 'formatting'
        });
      // T
      case 'eeeee':
        return localize.day(dayOfWeek, {
          width: 'narrow',
          context: 'formatting'
        });
      // Tu
      case 'eeeeee':
        return localize.day(dayOfWeek, {
          width: 'short',
          context: 'formatting'
        });
      // Tuesday
      case 'eeee':
      default:
        return localize.day(dayOfWeek, {
          width: 'wide',
          context: 'formatting'
        });
    }
  },
  // Stand-alone local day of week
  c: function c(date, token, localize, options) {
    var dayOfWeek = date.getUTCDay();
    var localDayOfWeek = (dayOfWeek - options.weekStartsOn + 8) % 7 || 7;
    switch (token) {
      // Numerical value (same as in `e`)
      case 'c':
        return String(localDayOfWeek);
      // Padded numerical value
      case 'cc':
        return addLeadingZeros(localDayOfWeek, token.length);
      // 1st, 2nd, ..., 7th
      case 'co':
        return localize.ordinalNumber(localDayOfWeek, {
          unit: 'day'
        });
      case 'ccc':
        return localize.day(dayOfWeek, {
          width: 'abbreviated',
          context: 'standalone'
        });
      // T
      case 'ccccc':
        return localize.day(dayOfWeek, {
          width: 'narrow',
          context: 'standalone'
        });
      // Tu
      case 'cccccc':
        return localize.day(dayOfWeek, {
          width: 'short',
          context: 'standalone'
        });
      // Tuesday
      case 'cccc':
      default:
        return localize.day(dayOfWeek, {
          width: 'wide',
          context: 'standalone'
        });
    }
  },
  // ISO day of week
  i: function i(date, token, localize) {
    var dayOfWeek = date.getUTCDay();
    var isoDayOfWeek = dayOfWeek === 0 ? 7 : dayOfWeek;
    switch (token) {
      // 2
      case 'i':
        return String(isoDayOfWeek);
      // 02
      case 'ii':
        return addLeadingZeros(isoDayOfWeek, token.length);
      // 2nd
      case 'io':
        return localize.ordinalNumber(isoDayOfWeek, {
          unit: 'day'
        });
      // Tue
      case 'iii':
        return localize.day(dayOfWeek, {
          width: 'abbreviated',
          context: 'formatting'
        });
      // T
      case 'iiiii':
        return localize.day(dayOfWeek, {
          width: 'narrow',
          context: 'formatting'
        });
      // Tu
      case 'iiiiii':
        return localize.day(dayOfWeek, {
          width: 'short',
          context: 'formatting'
        });
      // Tuesday
      case 'iiii':
      default:
        return localize.day(dayOfWeek, {
          width: 'wide',
          context: 'formatting'
        });
    }
  },
  // AM or PM
  a: function a(date, token, localize) {
    var hours = date.getUTCHours();
    var dayPeriodEnumValue = hours / 12 >= 1 ? 'pm' : 'am';
    switch (token) {
      case 'a':
      case 'aa':
        return localize.dayPeriod(dayPeriodEnumValue, {
          width: 'abbreviated',
          context: 'formatting'
        });
      case 'aaa':
        return localize.dayPeriod(dayPeriodEnumValue, {
          width: 'abbreviated',
          context: 'formatting'
        }).toLowerCase();
      case 'aaaaa':
        return localize.dayPeriod(dayPeriodEnumValue, {
          width: 'narrow',
          context: 'formatting'
        });
      case 'aaaa':
      default:
        return localize.dayPeriod(dayPeriodEnumValue, {
          width: 'wide',
          context: 'formatting'
        });
    }
  },
  // AM, PM, midnight, noon
  b: function b(date, token, localize) {
    var hours = date.getUTCHours();
    var dayPeriodEnumValue;
    if (hours === 12) {
      dayPeriodEnumValue = dayPeriodEnum.noon;
    } else if (hours === 0) {
      dayPeriodEnumValue = dayPeriodEnum.midnight;
    } else {
      dayPeriodEnumValue = hours / 12 >= 1 ? 'pm' : 'am';
    }
    switch (token) {
      case 'b':
      case 'bb':
        return localize.dayPeriod(dayPeriodEnumValue, {
          width: 'abbreviated',
          context: 'formatting'
        });
      case 'bbb':
        return localize.dayPeriod(dayPeriodEnumValue, {
          width: 'abbreviated',
          context: 'formatting'
        }).toLowerCase();
      case 'bbbbb':
        return localize.dayPeriod(dayPeriodEnumValue, {
          width: 'narrow',
          context: 'formatting'
        });
      case 'bbbb':
      default:
        return localize.dayPeriod(dayPeriodEnumValue, {
          width: 'wide',
          context: 'formatting'
        });
    }
  },
  // in the morning, in the afternoon, in the evening, at night
  B: function B(date, token, localize) {
    var hours = date.getUTCHours();
    var dayPeriodEnumValue;
    if (hours >= 17) {
      dayPeriodEnumValue = dayPeriodEnum.evening;
    } else if (hours >= 12) {
      dayPeriodEnumValue = dayPeriodEnum.afternoon;
    } else if (hours >= 4) {
      dayPeriodEnumValue = dayPeriodEnum.morning;
    } else {
      dayPeriodEnumValue = dayPeriodEnum.night;
    }
    switch (token) {
      case 'B':
      case 'BB':
      case 'BBB':
        return localize.dayPeriod(dayPeriodEnumValue, {
          width: 'abbreviated',
          context: 'formatting'
        });
      case 'BBBBB':
        return localize.dayPeriod(dayPeriodEnumValue, {
          width: 'narrow',
          context: 'formatting'
        });
      case 'BBBB':
      default:
        return localize.dayPeriod(dayPeriodEnumValue, {
          width: 'wide',
          context: 'formatting'
        });
    }
  },
  // Hour [1-12]
  h: function h(date, token, localize) {
    if (token === 'ho') {
      var hours = date.getUTCHours() % 12;
      if (hours === 0) hours = 12;
      return localize.ordinalNumber(hours, {
        unit: 'hour'
      });
    }
    return formatters$3.h(date, token);
  },
  // Hour [0-23]
  H: function H(date, token, localize) {
    if (token === 'Ho') {
      return localize.ordinalNumber(date.getUTCHours(), {
        unit: 'hour'
      });
    }
    return formatters$3.H(date, token);
  },
  // Hour [0-11]
  K: function K(date, token, localize) {
    var hours = date.getUTCHours() % 12;
    if (token === 'Ko') {
      return localize.ordinalNumber(hours, {
        unit: 'hour'
      });
    }
    return addLeadingZeros(hours, token.length);
  },
  // Hour [1-24]
  k: function k(date, token, localize) {
    var hours = date.getUTCHours();
    if (hours === 0) hours = 24;
    if (token === 'ko') {
      return localize.ordinalNumber(hours, {
        unit: 'hour'
      });
    }
    return addLeadingZeros(hours, token.length);
  },
  // Minute
  m: function m(date, token, localize) {
    if (token === 'mo') {
      return localize.ordinalNumber(date.getUTCMinutes(), {
        unit: 'minute'
      });
    }
    return formatters$3.m(date, token);
  },
  // Second
  s: function s(date, token, localize) {
    if (token === 'so') {
      return localize.ordinalNumber(date.getUTCSeconds(), {
        unit: 'second'
      });
    }
    return formatters$3.s(date, token);
  },
  // Fraction of second
  S: function S(date, token) {
    return formatters$3.S(date, token);
  },
  // Timezone (ISO-8601. If offset is 0, output is always `'Z'`)
  X: function X(date, token, _localize, options) {
    var originalDate = options._originalDate || date;
    var timezoneOffset = originalDate.getTimezoneOffset();
    if (timezoneOffset === 0) {
      return 'Z';
    }
    switch (token) {
      // Hours and optional minutes
      case 'X':
        return formatTimezoneWithOptionalMinutes(timezoneOffset);

      // Hours, minutes and optional seconds without `:` delimiter
      // Note: neither ISO-8601 nor JavaScript supports seconds in timezone offsets
      // so this token always has the same output as `XX`
      case 'XXXX':
      case 'XX':
        // Hours and minutes without `:` delimiter
        return formatTimezone(timezoneOffset);

      // Hours, minutes and optional seconds with `:` delimiter
      // Note: neither ISO-8601 nor JavaScript supports seconds in timezone offsets
      // so this token always has the same output as `XXX`
      case 'XXXXX':
      case 'XXX': // Hours and minutes with `:` delimiter
      default:
        return formatTimezone(timezoneOffset, ':');
    }
  },
  // Timezone (ISO-8601. If offset is 0, output is `'+00:00'` or equivalent)
  x: function x(date, token, _localize, options) {
    var originalDate = options._originalDate || date;
    var timezoneOffset = originalDate.getTimezoneOffset();
    switch (token) {
      // Hours and optional minutes
      case 'x':
        return formatTimezoneWithOptionalMinutes(timezoneOffset);

      // Hours, minutes and optional seconds without `:` delimiter
      // Note: neither ISO-8601 nor JavaScript supports seconds in timezone offsets
      // so this token always has the same output as `xx`
      case 'xxxx':
      case 'xx':
        // Hours and minutes without `:` delimiter
        return formatTimezone(timezoneOffset);

      // Hours, minutes and optional seconds with `:` delimiter
      // Note: neither ISO-8601 nor JavaScript supports seconds in timezone offsets
      // so this token always has the same output as `xxx`
      case 'xxxxx':
      case 'xxx': // Hours and minutes with `:` delimiter
      default:
        return formatTimezone(timezoneOffset, ':');
    }
  },
  // Timezone (GMT)
  O: function O(date, token, _localize, options) {
    var originalDate = options._originalDate || date;
    var timezoneOffset = originalDate.getTimezoneOffset();
    switch (token) {
      // Short
      case 'O':
      case 'OO':
      case 'OOO':
        return 'GMT' + formatTimezoneShort(timezoneOffset, ':');
      // Long
      case 'OOOO':
      default:
        return 'GMT' + formatTimezone(timezoneOffset, ':');
    }
  },
  // Timezone (specific non-location)
  z: function z(date, token, _localize, options) {
    var originalDate = options._originalDate || date;
    var timezoneOffset = originalDate.getTimezoneOffset();
    switch (token) {
      // Short
      case 'z':
      case 'zz':
      case 'zzz':
        return 'GMT' + formatTimezoneShort(timezoneOffset, ':');
      // Long
      case 'zzzz':
      default:
        return 'GMT' + formatTimezone(timezoneOffset, ':');
    }
  },
  // Seconds timestamp
  t: function t(date, token, _localize, options) {
    var originalDate = options._originalDate || date;
    var timestamp = Math.floor(originalDate.getTime() / 1000);
    return addLeadingZeros(timestamp, token.length);
  },
  // Milliseconds timestamp
  T: function T(date, token, _localize, options) {
    var originalDate = options._originalDate || date;
    var timestamp = originalDate.getTime();
    return addLeadingZeros(timestamp, token.length);
  }
};
function formatTimezoneShort(offset, dirtyDelimiter) {
  var sign = offset > 0 ? '-' : '+';
  var absOffset = Math.abs(offset);
  var hours = Math.floor(absOffset / 60);
  var minutes = absOffset % 60;
  if (minutes === 0) {
    return sign + String(hours);
  }
  var delimiter = dirtyDelimiter || '';
  return sign + String(hours) + delimiter + addLeadingZeros(minutes, 2);
}
function formatTimezoneWithOptionalMinutes(offset, dirtyDelimiter) {
  if (offset % 60 === 0) {
    var sign = offset > 0 ? '-' : '+';
    return sign + addLeadingZeros(Math.abs(offset) / 60, 2);
  }
  return formatTimezone(offset, dirtyDelimiter);
}
function formatTimezone(offset, dirtyDelimiter) {
  var delimiter = dirtyDelimiter || '';
  var sign = offset > 0 ? '-' : '+';
  var absOffset = Math.abs(offset);
  var hours = addLeadingZeros(Math.floor(absOffset / 60), 2);
  var minutes = addLeadingZeros(absOffset % 60, 2);
  return sign + hours + delimiter + minutes;
}
var formatters$1 = formatters;

var dateLongFormatter = function dateLongFormatter(pattern, formatLong) {
  switch (pattern) {
    case 'P':
      return formatLong.date({
        width: 'short'
      });
    case 'PP':
      return formatLong.date({
        width: 'medium'
      });
    case 'PPP':
      return formatLong.date({
        width: 'long'
      });
    case 'PPPP':
    default:
      return formatLong.date({
        width: 'full'
      });
  }
};
var timeLongFormatter = function timeLongFormatter(pattern, formatLong) {
  switch (pattern) {
    case 'p':
      return formatLong.time({
        width: 'short'
      });
    case 'pp':
      return formatLong.time({
        width: 'medium'
      });
    case 'ppp':
      return formatLong.time({
        width: 'long'
      });
    case 'pppp':
    default:
      return formatLong.time({
        width: 'full'
      });
  }
};
var dateTimeLongFormatter = function dateTimeLongFormatter(pattern, formatLong) {
  var matchResult = pattern.match(/(P+)(p+)?/) || [];
  var datePattern = matchResult[1];
  var timePattern = matchResult[2];
  if (!timePattern) {
    return dateLongFormatter(pattern, formatLong);
  }
  var dateTimeFormat;
  switch (datePattern) {
    case 'P':
      dateTimeFormat = formatLong.dateTime({
        width: 'short'
      });
      break;
    case 'PP':
      dateTimeFormat = formatLong.dateTime({
        width: 'medium'
      });
      break;
    case 'PPP':
      dateTimeFormat = formatLong.dateTime({
        width: 'long'
      });
      break;
    case 'PPPP':
    default:
      dateTimeFormat = formatLong.dateTime({
        width: 'full'
      });
      break;
  }
  return dateTimeFormat.replace('{{date}}', dateLongFormatter(datePattern, formatLong)).replace('{{time}}', timeLongFormatter(timePattern, formatLong));
};
var longFormatters = {
  p: timeLongFormatter,
  P: dateTimeLongFormatter
};
var longFormatters$1 = longFormatters;

var protectedDayOfYearTokens = ['D', 'DD'];
var protectedWeekYearTokens = ['YY', 'YYYY'];
function isProtectedDayOfYearToken(token) {
  return protectedDayOfYearTokens.indexOf(token) !== -1;
}
function isProtectedWeekYearToken(token) {
  return protectedWeekYearTokens.indexOf(token) !== -1;
}
function throwProtectedError(token, format, input) {
  if (token === 'YYYY') {
    throw new RangeError("Use `yyyy` instead of `YYYY` (in `".concat(format, "`) for formatting years to the input `").concat(input, "`; see: https://github.com/date-fns/date-fns/blob/master/docs/unicodeTokens.md"));
  } else if (token === 'YY') {
    throw new RangeError("Use `yy` instead of `YY` (in `".concat(format, "`) for formatting years to the input `").concat(input, "`; see: https://github.com/date-fns/date-fns/blob/master/docs/unicodeTokens.md"));
  } else if (token === 'D') {
    throw new RangeError("Use `d` instead of `D` (in `".concat(format, "`) for formatting days of the month to the input `").concat(input, "`; see: https://github.com/date-fns/date-fns/blob/master/docs/unicodeTokens.md"));
  } else if (token === 'DD') {
    throw new RangeError("Use `dd` instead of `DD` (in `".concat(format, "`) for formatting days of the month to the input `").concat(input, "`; see: https://github.com/date-fns/date-fns/blob/master/docs/unicodeTokens.md"));
  }
}

var formatDistanceLocale = {
  lessThanXSeconds: {
    one: 'less than a second',
    other: 'less than {{count}} seconds'
  },
  xSeconds: {
    one: '1 second',
    other: '{{count}} seconds'
  },
  halfAMinute: 'half a minute',
  lessThanXMinutes: {
    one: 'less than a minute',
    other: 'less than {{count}} minutes'
  },
  xMinutes: {
    one: '1 minute',
    other: '{{count}} minutes'
  },
  aboutXHours: {
    one: 'about 1 hour',
    other: 'about {{count}} hours'
  },
  xHours: {
    one: '1 hour',
    other: '{{count}} hours'
  },
  xDays: {
    one: '1 day',
    other: '{{count}} days'
  },
  aboutXWeeks: {
    one: 'about 1 week',
    other: 'about {{count}} weeks'
  },
  xWeeks: {
    one: '1 week',
    other: '{{count}} weeks'
  },
  aboutXMonths: {
    one: 'about 1 month',
    other: 'about {{count}} months'
  },
  xMonths: {
    one: '1 month',
    other: '{{count}} months'
  },
  aboutXYears: {
    one: 'about 1 year',
    other: 'about {{count}} years'
  },
  xYears: {
    one: '1 year',
    other: '{{count}} years'
  },
  overXYears: {
    one: 'over 1 year',
    other: 'over {{count}} years'
  },
  almostXYears: {
    one: 'almost 1 year',
    other: 'almost {{count}} years'
  }
};
var formatDistance = function formatDistance(token, count, options) {
  var result;
  var tokenValue = formatDistanceLocale[token];
  if (typeof tokenValue === 'string') {
    result = tokenValue;
  } else if (count === 1) {
    result = tokenValue.one;
  } else {
    result = tokenValue.other.replace('{{count}}', count.toString());
  }
  if (options !== null && options !== void 0 && options.addSuffix) {
    if (options.comparison && options.comparison > 0) {
      return 'in ' + result;
    } else {
      return result + ' ago';
    }
  }
  return result;
};
var formatDistance$1 = formatDistance;

function buildFormatLongFn(args) {
  return function () {
    var options = arguments.length > 0 && arguments[0] !== undefined ? arguments[0] : {};
    // TODO: Remove String()
    var width = options.width ? String(options.width) : args.defaultWidth;
    var format = args.formats[width] || args.formats[args.defaultWidth];
    return format;
  };
}

var dateFormats = {
  full: 'EEEE, MMMM do, y',
  long: 'MMMM do, y',
  medium: 'MMM d, y',
  short: 'MM/dd/yyyy'
};
var timeFormats = {
  full: 'h:mm:ss a zzzz',
  long: 'h:mm:ss a z',
  medium: 'h:mm:ss a',
  short: 'h:mm a'
};
var dateTimeFormats = {
  full: "{{date}} 'at' {{time}}",
  long: "{{date}} 'at' {{time}}",
  medium: '{{date}}, {{time}}',
  short: '{{date}}, {{time}}'
};
var formatLong = {
  date: buildFormatLongFn({
    formats: dateFormats,
    defaultWidth: 'full'
  }),
  time: buildFormatLongFn({
    formats: timeFormats,
    defaultWidth: 'full'
  }),
  dateTime: buildFormatLongFn({
    formats: dateTimeFormats,
    defaultWidth: 'full'
  })
};
var formatLong$1 = formatLong;

var formatRelativeLocale = {
  lastWeek: "'last' eeee 'at' p",
  yesterday: "'yesterday at' p",
  today: "'today at' p",
  tomorrow: "'tomorrow at' p",
  nextWeek: "eeee 'at' p",
  other: 'P'
};
var formatRelative = function formatRelative(token, _date, _baseDate, _options) {
  return formatRelativeLocale[token];
};
var formatRelative$1 = formatRelative;

function buildLocalizeFn(args) {
  return function (dirtyIndex, options) {
    var context = options !== null && options !== void 0 && options.context ? String(options.context) : 'standalone';
    var valuesArray;
    if (context === 'formatting' && args.formattingValues) {
      var defaultWidth = args.defaultFormattingWidth || args.defaultWidth;
      var width = options !== null && options !== void 0 && options.width ? String(options.width) : defaultWidth;
      valuesArray = args.formattingValues[width] || args.formattingValues[defaultWidth];
    } else {
      var _defaultWidth = args.defaultWidth;
      var _width = options !== null && options !== void 0 && options.width ? String(options.width) : args.defaultWidth;
      valuesArray = args.values[_width] || args.values[_defaultWidth];
    }
    var index = args.argumentCallback ? args.argumentCallback(dirtyIndex) : dirtyIndex;
    // @ts-ignore: For some reason TypeScript just don't want to match it, no matter how hard we try. I challenge you to try to remove it!
    return valuesArray[index];
  };
}

var eraValues = {
  narrow: ['B', 'A'],
  abbreviated: ['BC', 'AD'],
  wide: ['Before Christ', 'Anno Domini']
};
var quarterValues = {
  narrow: ['1', '2', '3', '4'],
  abbreviated: ['Q1', 'Q2', 'Q3', 'Q4'],
  wide: ['1st quarter', '2nd quarter', '3rd quarter', '4th quarter']
};

// Note: in English, the names of days of the week and months are capitalized.
// If you are making a new locale based on this one, check if the same is true for the language you're working on.
// Generally, formatted dates should look like they are in the middle of a sentence,
// e.g. in Spanish language the weekdays and months should be in the lowercase.
var monthValues = {
  narrow: ['J', 'F', 'M', 'A', 'M', 'J', 'J', 'A', 'S', 'O', 'N', 'D'],
  abbreviated: ['Jan', 'Feb', 'Mar', 'Apr', 'May', 'Jun', 'Jul', 'Aug', 'Sep', 'Oct', 'Nov', 'Dec'],
  wide: ['January', 'February', 'March', 'April', 'May', 'June', 'July', 'August', 'September', 'October', 'November', 'December']
};
var dayValues = {
  narrow: ['S', 'M', 'T', 'W', 'T', 'F', 'S'],
  short: ['Su', 'Mo', 'Tu', 'We', 'Th', 'Fr', 'Sa'],
  abbreviated: ['Sun', 'Mon', 'Tue', 'Wed', 'Thu', 'Fri', 'Sat'],
  wide: ['Sunday', 'Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday', 'Saturday']
};
var dayPeriodValues = {
  narrow: {
    am: 'a',
    pm: 'p',
    midnight: 'mi',
    noon: 'n',
    morning: 'morning',
    afternoon: 'afternoon',
    evening: 'evening',
    night: 'night'
  },
  abbreviated: {
    am: 'AM',
    pm: 'PM',
    midnight: 'midnight',
    noon: 'noon',
    morning: 'morning',
    afternoon: 'afternoon',
    evening: 'evening',
    night: 'night'
  },
  wide: {
    am: 'a.m.',
    pm: 'p.m.',
    midnight: 'midnight',
    noon: 'noon',
    morning: 'morning',
    afternoon: 'afternoon',
    evening: 'evening',
    night: 'night'
  }
};
var formattingDayPeriodValues = {
  narrow: {
    am: 'a',
    pm: 'p',
    midnight: 'mi',
    noon: 'n',
    morning: 'in the morning',
    afternoon: 'in the afternoon',
    evening: 'in the evening',
    night: 'at night'
  },
  abbreviated: {
    am: 'AM',
    pm: 'PM',
    midnight: 'midnight',
    noon: 'noon',
    morning: 'in the morning',
    afternoon: 'in the afternoon',
    evening: 'in the evening',
    night: 'at night'
  },
  wide: {
    am: 'a.m.',
    pm: 'p.m.',
    midnight: 'midnight',
    noon: 'noon',
    morning: 'in the morning',
    afternoon: 'in the afternoon',
    evening: 'in the evening',
    night: 'at night'
  }
};
var ordinalNumber = function ordinalNumber(dirtyNumber, _options) {
  var number = Number(dirtyNumber);

  // If ordinal numbers depend on context, for example,
  // if they are different for different grammatical genders,
  // use `options.unit`.
  //
  // `unit` can be 'year', 'quarter', 'month', 'week', 'date', 'dayOfYear',
  // 'day', 'hour', 'minute', 'second'.

  var rem100 = number % 100;
  if (rem100 > 20 || rem100 < 10) {
    switch (rem100 % 10) {
      case 1:
        return number + 'st';
      case 2:
        return number + 'nd';
      case 3:
        return number + 'rd';
    }
  }
  return number + 'th';
};
var localize = {
  ordinalNumber: ordinalNumber,
  era: buildLocalizeFn({
    values: eraValues,
    defaultWidth: 'wide'
  }),
  quarter: buildLocalizeFn({
    values: quarterValues,
    defaultWidth: 'wide',
    argumentCallback: function argumentCallback(quarter) {
      return quarter - 1;
    }
  }),
  month: buildLocalizeFn({
    values: monthValues,
    defaultWidth: 'wide'
  }),
  day: buildLocalizeFn({
    values: dayValues,
    defaultWidth: 'wide'
  }),
  dayPeriod: buildLocalizeFn({
    values: dayPeriodValues,
    defaultWidth: 'wide',
    formattingValues: formattingDayPeriodValues,
    defaultFormattingWidth: 'wide'
  })
};
var localize$1 = localize;

function buildMatchFn(args) {
  return function (string) {
    var options = arguments.length > 1 && arguments[1] !== undefined ? arguments[1] : {};
    var width = options.width;
    var matchPattern = width && args.matchPatterns[width] || args.matchPatterns[args.defaultMatchWidth];
    var matchResult = string.match(matchPattern);
    if (!matchResult) {
      return null;
    }
    var matchedString = matchResult[0];
    var parsePatterns = width && args.parsePatterns[width] || args.parsePatterns[args.defaultParseWidth];
    var key = Array.isArray(parsePatterns) ? findIndex(parsePatterns, function (pattern) {
      return pattern.test(matchedString);
    }) : findKey(parsePatterns, function (pattern) {
      return pattern.test(matchedString);
    });
    var value;
    value = args.valueCallback ? args.valueCallback(key) : key;
    value = options.valueCallback ? options.valueCallback(value) : value;
    var rest = string.slice(matchedString.length);
    return {
      value: value,
      rest: rest
    };
  };
}
function findKey(object, predicate) {
  for (var key in object) {
    if (object.hasOwnProperty(key) && predicate(object[key])) {
      return key;
    }
  }
  return undefined;
}
function findIndex(array, predicate) {
  for (var key = 0; key < array.length; key++) {
    if (predicate(array[key])) {
      return key;
    }
  }
  return undefined;
}

function buildMatchPatternFn(args) {
  return function (string) {
    var options = arguments.length > 1 && arguments[1] !== undefined ? arguments[1] : {};
    var matchResult = string.match(args.matchPattern);
    if (!matchResult) return null;
    var matchedString = matchResult[0];
    var parseResult = string.match(args.parsePattern);
    if (!parseResult) return null;
    var value = args.valueCallback ? args.valueCallback(parseResult[0]) : parseResult[0];
    value = options.valueCallback ? options.valueCallback(value) : value;
    var rest = string.slice(matchedString.length);
    return {
      value: value,
      rest: rest
    };
  };
}

var matchOrdinalNumberPattern = /^(\d+)(th|st|nd|rd)?/i;
var parseOrdinalNumberPattern = /\d+/i;
var matchEraPatterns = {
  narrow: /^(b|a)/i,
  abbreviated: /^(b\.?\s?c\.?|b\.?\s?c\.?\s?e\.?|a\.?\s?d\.?|c\.?\s?e\.?)/i,
  wide: /^(before christ|before common era|anno domini|common era)/i
};
var parseEraPatterns = {
  any: [/^b/i, /^(a|c)/i]
};
var matchQuarterPatterns = {
  narrow: /^[1234]/i,
  abbreviated: /^q[1234]/i,
  wide: /^[1234](th|st|nd|rd)? quarter/i
};
var parseQuarterPatterns = {
  any: [/1/i, /2/i, /3/i, /4/i]
};
var matchMonthPatterns = {
  narrow: /^[jfmasond]/i,
  abbreviated: /^(jan|feb|mar|apr|may|jun|jul|aug|sep|oct|nov|dec)/i,
  wide: /^(january|february|march|april|may|june|july|august|september|october|november|december)/i
};
var parseMonthPatterns = {
  narrow: [/^j/i, /^f/i, /^m/i, /^a/i, /^m/i, /^j/i, /^j/i, /^a/i, /^s/i, /^o/i, /^n/i, /^d/i],
  any: [/^ja/i, /^f/i, /^mar/i, /^ap/i, /^may/i, /^jun/i, /^jul/i, /^au/i, /^s/i, /^o/i, /^n/i, /^d/i]
};
var matchDayPatterns = {
  narrow: /^[smtwf]/i,
  short: /^(su|mo|tu|we|th|fr|sa)/i,
  abbreviated: /^(sun|mon|tue|wed|thu|fri|sat)/i,
  wide: /^(sunday|monday|tuesday|wednesday|thursday|friday|saturday)/i
};
var parseDayPatterns = {
  narrow: [/^s/i, /^m/i, /^t/i, /^w/i, /^t/i, /^f/i, /^s/i],
  any: [/^su/i, /^m/i, /^tu/i, /^w/i, /^th/i, /^f/i, /^sa/i]
};
var matchDayPeriodPatterns = {
  narrow: /^(a|p|mi|n|(in the|at) (morning|afternoon|evening|night))/i,
  any: /^([ap]\.?\s?m\.?|midnight|noon|(in the|at) (morning|afternoon|evening|night))/i
};
var parseDayPeriodPatterns = {
  any: {
    am: /^a/i,
    pm: /^p/i,
    midnight: /^mi/i,
    noon: /^no/i,
    morning: /morning/i,
    afternoon: /afternoon/i,
    evening: /evening/i,
    night: /night/i
  }
};
var match = {
  ordinalNumber: buildMatchPatternFn({
    matchPattern: matchOrdinalNumberPattern,
    parsePattern: parseOrdinalNumberPattern,
    valueCallback: function valueCallback(value) {
      return parseInt(value, 10);
    }
  }),
  era: buildMatchFn({
    matchPatterns: matchEraPatterns,
    defaultMatchWidth: 'wide',
    parsePatterns: parseEraPatterns,
    defaultParseWidth: 'any'
  }),
  quarter: buildMatchFn({
    matchPatterns: matchQuarterPatterns,
    defaultMatchWidth: 'wide',
    parsePatterns: parseQuarterPatterns,
    defaultParseWidth: 'any',
    valueCallback: function valueCallback(index) {
      return index + 1;
    }
  }),
  month: buildMatchFn({
    matchPatterns: matchMonthPatterns,
    defaultMatchWidth: 'wide',
    parsePatterns: parseMonthPatterns,
    defaultParseWidth: 'any'
  }),
  day: buildMatchFn({
    matchPatterns: matchDayPatterns,
    defaultMatchWidth: 'wide',
    parsePatterns: parseDayPatterns,
    defaultParseWidth: 'any'
  }),
  dayPeriod: buildMatchFn({
    matchPatterns: matchDayPeriodPatterns,
    defaultMatchWidth: 'any',
    parsePatterns: parseDayPeriodPatterns,
    defaultParseWidth: 'any'
  })
};
var match$1 = match;

/**
 * @type {Locale}
 * @category Locales
 * @summary English locale (United States).
 * @language English
 * @iso-639-2 eng
 * @author Sasha Koss [@kossnocorp]{@link https://github.com/kossnocorp}
 * @author Lesha Koss [@leshakoss]{@link https://github.com/leshakoss}
 */
var locale = {
  code: 'en-US',
  formatDistance: formatDistance$1,
  formatLong: formatLong$1,
  formatRelative: formatRelative$1,
  localize: localize$1,
  match: match$1,
  options: {
    weekStartsOn: 0 /* Sunday */,
    firstWeekContainsDate: 1
  }
};
var defaultLocale = locale;

// - [yYQqMLwIdDecihHKkms]o matches any available ordinal number token
//   (one of the certain letters followed by `o`)
// - (\w)\1* matches any sequences of the same letter
// - '' matches two quote characters in a row
// - '(''|[^'])+('|$) matches anything surrounded by two quote characters ('),
//   except a single quote symbol, which ends the sequence.
//   Two quote characters do not end the sequence.
//   If there is no matching single quote
//   then the sequence will continue until the end of the string.
// - . matches any single character unmatched by previous parts of the RegExps
var formattingTokensRegExp = /[yYQqMLwIdDecihHKkms]o|(\w)\1*|''|'(''|[^'])+('|$)|./g;

// This RegExp catches symbols escaped by quotes, and also
// sequences of symbols P, p, and the combinations like `PPPPPPPppppp`
var longFormattingTokensRegExp = /P+p+|P+|p+|''|'(''|[^'])+('|$)|./g;
var escapedStringRegExp = /^'([^]*?)'?$/;
var doubleQuoteRegExp = /''/g;
var unescapedLatinCharacterRegExp = /[a-zA-Z]/;

/**
 * @name format
 * @category Common Helpers
 * @summary Format the date.
 *
 * @description
 * Return the formatted date string in the given format. The result may vary by locale.
 *
 * > ⚠️ Please note that the `format` tokens differ from Moment.js and other libraries.
 * > See: https://github.com/date-fns/date-fns/blob/master/docs/unicodeTokens.md
 *
 * The characters wrapped between two single quotes characters (') are escaped.
 * Two single quotes in a row, whether inside or outside a quoted sequence, represent a 'real' single quote.
 * (see the last example)
 *
 * Format of the string is based on Unicode Technical Standard #35:
 * https://www.unicode.org/reports/tr35/tr35-dates.html#Date_Field_Symbol_Table
 * with a few additions (see note 7 below the table).
 *
 * Accepted patterns:
 * | Unit                            | Pattern | Result examples                   | Notes |
 * |---------------------------------|---------|-----------------------------------|-------|
 * | Era                             | G..GGG  | AD, BC                            |       |
 * |                                 | GGGG    | Anno Domini, Before Christ        | 2     |
 * |                                 | GGGGG   | A, B                              |       |
 * | Calendar year                   | y       | 44, 1, 1900, 2017                 | 5     |
 * |                                 | yo      | 44th, 1st, 0th, 17th              | 5,7   |
 * |                                 | yy      | 44, 01, 00, 17                    | 5     |
 * |                                 | yyy     | 044, 001, 1900, 2017              | 5     |
 * |                                 | yyyy    | 0044, 0001, 1900, 2017            | 5     |
 * |                                 | yyyyy   | ...                               | 3,5   |
 * | Local week-numbering year       | Y       | 44, 1, 1900, 2017                 | 5     |
 * |                                 | Yo      | 44th, 1st, 1900th, 2017th         | 5,7   |
 * |                                 | YY      | 44, 01, 00, 17                    | 5,8   |
 * |                                 | YYY     | 044, 001, 1900, 2017              | 5     |
 * |                                 | YYYY    | 0044, 0001, 1900, 2017            | 5,8   |
 * |                                 | YYYYY   | ...                               | 3,5   |
 * | ISO week-numbering year         | R       | -43, 0, 1, 1900, 2017             | 5,7   |
 * |                                 | RR      | -43, 00, 01, 1900, 2017           | 5,7   |
 * |                                 | RRR     | -043, 000, 001, 1900, 2017        | 5,7   |
 * |                                 | RRRR    | -0043, 0000, 0001, 1900, 2017     | 5,7   |
 * |                                 | RRRRR   | ...                               | 3,5,7 |
 * | Extended year                   | u       | -43, 0, 1, 1900, 2017             | 5     |
 * |                                 | uu      | -43, 01, 1900, 2017               | 5     |
 * |                                 | uuu     | -043, 001, 1900, 2017             | 5     |
 * |                                 | uuuu    | -0043, 0001, 1900, 2017           | 5     |
 * |                                 | uuuuu   | ...                               | 3,5   |
 * | Quarter (formatting)            | Q       | 1, 2, 3, 4                        |       |
 * |                                 | Qo      | 1st, 2nd, 3rd, 4th                | 7     |
 * |                                 | QQ      | 01, 02, 03, 04                    |       |
 * |                                 | QQQ     | Q1, Q2, Q3, Q4                    |       |
 * |                                 | QQQQ    | 1st quarter, 2nd quarter, ...     | 2     |
 * |                                 | QQQQQ   | 1, 2, 3, 4                        | 4     |
 * | Quarter (stand-alone)           | q       | 1, 2, 3, 4                        |       |
 * |                                 | qo      | 1st, 2nd, 3rd, 4th                | 7     |
 * |                                 | qq      | 01, 02, 03, 04                    |       |
 * |                                 | qqq     | Q1, Q2, Q3, Q4                    |       |
 * |                                 | qqqq    | 1st quarter, 2nd quarter, ...     | 2     |
 * |                                 | qqqqq   | 1, 2, 3, 4                        | 4     |
 * | Month (formatting)              | M       | 1, 2, ..., 12                     |       |
 * |                                 | Mo      | 1st, 2nd, ..., 12th               | 7     |
 * |                                 | MM      | 01, 02, ..., 12                   |       |
 * |                                 | MMM     | Jan, Feb, ..., Dec                |       |
 * |                                 | MMMM    | January, February, ..., December  | 2     |
 * |                                 | MMMMM   | J, F, ..., D                      |       |
 * | Month (stand-alone)             | L       | 1, 2, ..., 12                     |       |
 * |                                 | Lo      | 1st, 2nd, ..., 12th               | 7     |
 * |                                 | LL      | 01, 02, ..., 12                   |       |
 * |                                 | LLL     | Jan, Feb, ..., Dec                |       |
 * |                                 | LLLL    | January, February, ..., December  | 2     |
 * |                                 | LLLLL   | J, F, ..., D                      |       |
 * | Local week of year              | w       | 1, 2, ..., 53                     |       |
 * |                                 | wo      | 1st, 2nd, ..., 53th               | 7     |
 * |                                 | ww      | 01, 02, ..., 53                   |       |
 * | ISO week of year                | I       | 1, 2, ..., 53                     | 7     |
 * |                                 | Io      | 1st, 2nd, ..., 53th               | 7     |
 * |                                 | II      | 01, 02, ..., 53                   | 7     |
 * | Day of month                    | d       | 1, 2, ..., 31                     |       |
 * |                                 | do      | 1st, 2nd, ..., 31st               | 7     |
 * |                                 | dd      | 01, 02, ..., 31                   |       |
 * | Day of year                     | D       | 1, 2, ..., 365, 366               | 9     |
 * |                                 | Do      | 1st, 2nd, ..., 365th, 366th       | 7     |
 * |                                 | DD      | 01, 02, ..., 365, 366             | 9     |
 * |                                 | DDD     | 001, 002, ..., 365, 366           |       |
 * |                                 | DDDD    | ...                               | 3     |
 * | Day of week (formatting)        | E..EEE  | Mon, Tue, Wed, ..., Sun           |       |
 * |                                 | EEEE    | Monday, Tuesday, ..., Sunday      | 2     |
 * |                                 | EEEEE   | M, T, W, T, F, S, S               |       |
 * |                                 | EEEEEE  | Mo, Tu, We, Th, Fr, Sa, Su        |       |
 * | ISO day of week (formatting)    | i       | 1, 2, 3, ..., 7                   | 7     |
 * |                                 | io      | 1st, 2nd, ..., 7th                | 7     |
 * |                                 | ii      | 01, 02, ..., 07                   | 7     |
 * |                                 | iii     | Mon, Tue, Wed, ..., Sun           | 7     |
 * |                                 | iiii    | Monday, Tuesday, ..., Sunday      | 2,7   |
 * |                                 | iiiii   | M, T, W, T, F, S, S               | 7     |
 * |                                 | iiiiii  | Mo, Tu, We, Th, Fr, Sa, Su        | 7     |
 * | Local day of week (formatting)  | e       | 2, 3, 4, ..., 1                   |       |
 * |                                 | eo      | 2nd, 3rd, ..., 1st                | 7     |
 * |                                 | ee      | 02, 03, ..., 01                   |       |
 * |                                 | eee     | Mon, Tue, Wed, ..., Sun           |       |
 * |                                 | eeee    | Monday, Tuesday, ..., Sunday      | 2     |
 * |                                 | eeeee   | M, T, W, T, F, S, S               |       |
 * |                                 | eeeeee  | Mo, Tu, We, Th, Fr, Sa, Su        |       |
 * | Local day of week (stand-alone) | c       | 2, 3, 4, ..., 1                   |       |
 * |                                 | co      | 2nd, 3rd, ..., 1st                | 7     |
 * |                                 | cc      | 02, 03, ..., 01                   |       |
 * |                                 | ccc     | Mon, Tue, Wed, ..., Sun           |       |
 * |                                 | cccc    | Monday, Tuesday, ..., Sunday      | 2     |
 * |                                 | ccccc   | M, T, W, T, F, S, S               |       |
 * |                                 | cccccc  | Mo, Tu, We, Th, Fr, Sa, Su        |       |
 * | AM, PM                          | a..aa   | AM, PM                            |       |
 * |                                 | aaa     | am, pm                            |       |
 * |                                 | aaaa    | a.m., p.m.                        | 2     |
 * |                                 | aaaaa   | a, p                              |       |
 * | AM, PM, noon, midnight          | b..bb   | AM, PM, noon, midnight            |       |
 * |                                 | bbb     | am, pm, noon, midnight            |       |
 * |                                 | bbbb    | a.m., p.m., noon, midnight        | 2     |
 * |                                 | bbbbb   | a, p, n, mi                       |       |
 * | Flexible day period             | B..BBB  | at night, in the morning, ...     |       |
 * |                                 | BBBB    | at night, in the morning, ...     | 2     |
 * |                                 | BBBBB   | at night, in the morning, ...     |       |
 * | Hour [1-12]                     | h       | 1, 2, ..., 11, 12                 |       |
 * |                                 | ho      | 1st, 2nd, ..., 11th, 12th         | 7     |
 * |                                 | hh      | 01, 02, ..., 11, 12               |       |
 * | Hour [0-23]                     | H       | 0, 1, 2, ..., 23                  |       |
 * |                                 | Ho      | 0th, 1st, 2nd, ..., 23rd          | 7     |
 * |                                 | HH      | 00, 01, 02, ..., 23               |       |
 * | Hour [0-11]                     | K       | 1, 2, ..., 11, 0                  |       |
 * |                                 | Ko      | 1st, 2nd, ..., 11th, 0th          | 7     |
 * |                                 | KK      | 01, 02, ..., 11, 00               |       |
 * | Hour [1-24]                     | k       | 24, 1, 2, ..., 23                 |       |
 * |                                 | ko      | 24th, 1st, 2nd, ..., 23rd         | 7     |
 * |                                 | kk      | 24, 01, 02, ..., 23               |       |
 * | Minute                          | m       | 0, 1, ..., 59                     |       |
 * |                                 | mo      | 0th, 1st, ..., 59th               | 7     |
 * |                                 | mm      | 00, 01, ..., 59                   |       |
 * | Second                          | s       | 0, 1, ..., 59                     |       |
 * |                                 | so      | 0th, 1st, ..., 59th               | 7     |
 * |                                 | ss      | 00, 01, ..., 59                   |       |
 * | Fraction of second              | S       | 0, 1, ..., 9                      |       |
 * |                                 | SS      | 00, 01, ..., 99                   |       |
 * |                                 | SSS     | 000, 001, ..., 999                |       |
 * |                                 | SSSS    | ...                               | 3     |
 * | Timezone (ISO-8601 w/ Z)        | X       | -08, +0530, Z                     |       |
 * |                                 | XX      | -0800, +0530, Z                   |       |
 * |                                 | XXX     | -08:00, +05:30, Z                 |       |
 * |                                 | XXXX    | -0800, +0530, Z, +123456          | 2     |
 * |                                 | XXXXX   | -08:00, +05:30, Z, +12:34:56      |       |
 * | Timezone (ISO-8601 w/o Z)       | x       | -08, +0530, +00                   |       |
 * |                                 | xx      | -0800, +0530, +0000               |       |
 * |                                 | xxx     | -08:00, +05:30, +00:00            | 2     |
 * |                                 | xxxx    | -0800, +0530, +0000, +123456      |       |
 * |                                 | xxxxx   | -08:00, +05:30, +00:00, +12:34:56 |       |
 * | Timezone (GMT)                  | O...OOO | GMT-8, GMT+5:30, GMT+0            |       |
 * |                                 | OOOO    | GMT-08:00, GMT+05:30, GMT+00:00   | 2     |
 * | Timezone (specific non-locat.)  | z...zzz | GMT-8, GMT+5:30, GMT+0            | 6     |
 * |                                 | zzzz    | GMT-08:00, GMT+05:30, GMT+00:00   | 2,6   |
 * | Seconds timestamp               | t       | 512969520                         | 7     |
 * |                                 | tt      | ...                               | 3,7   |
 * | Milliseconds timestamp          | T       | 512969520900                      | 7     |
 * |                                 | TT      | ...                               | 3,7   |
 * | Long localized date             | P       | 04/29/1453                        | 7     |
 * |                                 | PP      | Apr 29, 1453                      | 7     |
 * |                                 | PPP     | April 29th, 1453                  | 7     |
 * |                                 | PPPP    | Friday, April 29th, 1453          | 2,7   |
 * | Long localized time             | p       | 12:00 AM                          | 7     |
 * |                                 | pp      | 12:00:00 AM                       | 7     |
 * |                                 | ppp     | 12:00:00 AM GMT+2                 | 7     |
 * |                                 | pppp    | 12:00:00 AM GMT+02:00             | 2,7   |
 * | Combination of date and time    | Pp      | 04/29/1453, 12:00 AM              | 7     |
 * |                                 | PPpp    | Apr 29, 1453, 12:00:00 AM         | 7     |
 * |                                 | PPPppp  | April 29th, 1453 at ...           | 7     |
 * |                                 | PPPPpppp| Friday, April 29th, 1453 at ...   | 2,7   |
 * Notes:
 * 1. "Formatting" units (e.g. formatting quarter) in the default en-US locale
 *    are the same as "stand-alone" units, but are different in some languages.
 *    "Formatting" units are declined according to the rules of the language
 *    in the context of a date. "Stand-alone" units are always nominative singular:
 *
 *    `format(new Date(2017, 10, 6), 'do LLLL', {locale: cs}) //=> '6. listopad'`
 *
 *    `format(new Date(2017, 10, 6), 'do MMMM', {locale: cs}) //=> '6. listopadu'`
 *
 * 2. Any sequence of the identical letters is a pattern, unless it is escaped by
 *    the single quote characters (see below).
 *    If the sequence is longer than listed in table (e.g. `EEEEEEEEEEE`)
 *    the output will be the same as default pattern for this unit, usually
 *    the longest one (in case of ISO weekdays, `EEEE`). Default patterns for units
 *    are marked with "2" in the last column of the table.
 *
 *    `format(new Date(2017, 10, 6), 'MMM') //=> 'Nov'`
 *
 *    `format(new Date(2017, 10, 6), 'MMMM') //=> 'November'`
 *
 *    `format(new Date(2017, 10, 6), 'MMMMM') //=> 'N'`
 *
 *    `format(new Date(2017, 10, 6), 'MMMMMM') //=> 'November'`
 *
 *    `format(new Date(2017, 10, 6), 'MMMMMMM') //=> 'November'`
 *
 * 3. Some patterns could be unlimited length (such as `yyyyyyyy`).
 *    The output will be padded with zeros to match the length of the pattern.
 *
 *    `format(new Date(2017, 10, 6), 'yyyyyyyy') //=> '00002017'`
 *
 * 4. `QQQQQ` and `qqqqq` could be not strictly numerical in some locales.
 *    These tokens represent the shortest form of the quarter.
 *
 * 5. The main difference between `y` and `u` patterns are B.C. years:
 *
 *    | Year | `y` | `u` |
 *    |------|-----|-----|
 *    | AC 1 |   1 |   1 |
 *    | BC 1 |   1 |   0 |
 *    | BC 2 |   2 |  -1 |
 *
 *    Also `yy` always returns the last two digits of a year,
 *    while `uu` pads single digit years to 2 characters and returns other years unchanged:
 *
 *    | Year | `yy` | `uu` |
 *    |------|------|------|
 *    | 1    |   01 |   01 |
 *    | 14   |   14 |   14 |
 *    | 376  |   76 |  376 |
 *    | 1453 |   53 | 1453 |
 *
 *    The same difference is true for local and ISO week-numbering years (`Y` and `R`),
 *    except local week-numbering years are dependent on `options.weekStartsOn`
 *    and `options.firstWeekContainsDate` (compare [getISOWeekYear]{@link https://date-fns.org/docs/getISOWeekYear}
 *    and [getWeekYear]{@link https://date-fns.org/docs/getWeekYear}).
 *
 * 6. Specific non-location timezones are currently unavailable in `date-fns`,
 *    so right now these tokens fall back to GMT timezones.
 *
 * 7. These patterns are not in the Unicode Technical Standard #35:
 *    - `i`: ISO day of week
 *    - `I`: ISO week of year
 *    - `R`: ISO week-numbering year
 *    - `t`: seconds timestamp
 *    - `T`: milliseconds timestamp
 *    - `o`: ordinal number modifier
 *    - `P`: long localized date
 *    - `p`: long localized time
 *
 * 8. `YY` and `YYYY` tokens represent week-numbering years but they are often confused with years.
 *    You should enable `options.useAdditionalWeekYearTokens` to use them. See: https://github.com/date-fns/date-fns/blob/master/docs/unicodeTokens.md
 *
 * 9. `D` and `DD` tokens represent days of the year but they are often confused with days of the month.
 *    You should enable `options.useAdditionalDayOfYearTokens` to use them. See: https://github.com/date-fns/date-fns/blob/master/docs/unicodeTokens.md
 *
 * @param {Date|Number} date - the original date
 * @param {String} format - the string of tokens
 * @param {Object} [options] - an object with options.
 * @param {Locale} [options.locale=defaultLocale] - the locale object. See [Locale]{@link https://date-fns.org/docs/Locale}
 * @param {0|1|2|3|4|5|6} [options.weekStartsOn=0] - the index of the first day of the week (0 - Sunday)
 * @param {Number} [options.firstWeekContainsDate=1] - the day of January, which is
 * @param {Boolean} [options.useAdditionalWeekYearTokens=false] - if true, allows usage of the week-numbering year tokens `YY` and `YYYY`;
 *   see: https://github.com/date-fns/date-fns/blob/master/docs/unicodeTokens.md
 * @param {Boolean} [options.useAdditionalDayOfYearTokens=false] - if true, allows usage of the day of year tokens `D` and `DD`;
 *   see: https://github.com/date-fns/date-fns/blob/master/docs/unicodeTokens.md
 * @returns {String} the formatted date string
 * @throws {TypeError} 2 arguments required
 * @throws {RangeError} `date` must not be Invalid Date
 * @throws {RangeError} `options.locale` must contain `localize` property
 * @throws {RangeError} `options.locale` must contain `formatLong` property
 * @throws {RangeError} `options.weekStartsOn` must be between 0 and 6
 * @throws {RangeError} `options.firstWeekContainsDate` must be between 1 and 7
 * @throws {RangeError} use `yyyy` instead of `YYYY` for formatting years using [format provided] to the input [input provided]; see: https://github.com/date-fns/date-fns/blob/master/docs/unicodeTokens.md
 * @throws {RangeError} use `yy` instead of `YY` for formatting years using [format provided] to the input [input provided]; see: https://github.com/date-fns/date-fns/blob/master/docs/unicodeTokens.md
 * @throws {RangeError} use `d` instead of `D` for formatting days of the month using [format provided] to the input [input provided]; see: https://github.com/date-fns/date-fns/blob/master/docs/unicodeTokens.md
 * @throws {RangeError} use `dd` instead of `DD` for formatting days of the month using [format provided] to the input [input provided]; see: https://github.com/date-fns/date-fns/blob/master/docs/unicodeTokens.md
 * @throws {RangeError} format string contains an unescaped latin alphabet character
 *
 * @example
 * // Represent 11 February 2014 in middle-endian format:
 * const result = format(new Date(2014, 1, 11), 'MM/dd/yyyy')
 * //=> '02/11/2014'
 *
 * @example
 * // Represent 2 July 2014 in Esperanto:
 * import { eoLocale } from 'date-fns/locale/eo'
 * const result = format(new Date(2014, 6, 2), "do 'de' MMMM yyyy", {
 *   locale: eoLocale
 * })
 * //=> '2-a de julio 2014'
 *
 * @example
 * // Escape string by single quote characters:
 * const result = format(new Date(2014, 6, 2, 15), "h 'o''clock'")
 * //=> "3 o'clock"
 */

function format(dirtyDate, dirtyFormatStr, options) {
  var _ref, _options$locale, _ref2, _ref3, _ref4, _options$firstWeekCon, _options$locale2, _options$locale2$opti, _defaultOptions$local, _defaultOptions$local2, _ref5, _ref6, _ref7, _options$weekStartsOn, _options$locale3, _options$locale3$opti, _defaultOptions$local3, _defaultOptions$local4;
  requiredArgs(2, arguments);
  var formatStr = String(dirtyFormatStr);
  var defaultOptions = getDefaultOptions();
  var locale = (_ref = (_options$locale = options === null || options === void 0 ? void 0 : options.locale) !== null && _options$locale !== void 0 ? _options$locale : defaultOptions.locale) !== null && _ref !== void 0 ? _ref : defaultLocale;
  var firstWeekContainsDate = toInteger((_ref2 = (_ref3 = (_ref4 = (_options$firstWeekCon = options === null || options === void 0 ? void 0 : options.firstWeekContainsDate) !== null && _options$firstWeekCon !== void 0 ? _options$firstWeekCon : options === null || options === void 0 ? void 0 : (_options$locale2 = options.locale) === null || _options$locale2 === void 0 ? void 0 : (_options$locale2$opti = _options$locale2.options) === null || _options$locale2$opti === void 0 ? void 0 : _options$locale2$opti.firstWeekContainsDate) !== null && _ref4 !== void 0 ? _ref4 : defaultOptions.firstWeekContainsDate) !== null && _ref3 !== void 0 ? _ref3 : (_defaultOptions$local = defaultOptions.locale) === null || _defaultOptions$local === void 0 ? void 0 : (_defaultOptions$local2 = _defaultOptions$local.options) === null || _defaultOptions$local2 === void 0 ? void 0 : _defaultOptions$local2.firstWeekContainsDate) !== null && _ref2 !== void 0 ? _ref2 : 1);

  // Test if weekStartsOn is between 1 and 7 _and_ is not NaN
  if (!(firstWeekContainsDate >= 1 && firstWeekContainsDate <= 7)) {
    throw new RangeError('firstWeekContainsDate must be between 1 and 7 inclusively');
  }
  var weekStartsOn = toInteger((_ref5 = (_ref6 = (_ref7 = (_options$weekStartsOn = options === null || options === void 0 ? void 0 : options.weekStartsOn) !== null && _options$weekStartsOn !== void 0 ? _options$weekStartsOn : options === null || options === void 0 ? void 0 : (_options$locale3 = options.locale) === null || _options$locale3 === void 0 ? void 0 : (_options$locale3$opti = _options$locale3.options) === null || _options$locale3$opti === void 0 ? void 0 : _options$locale3$opti.weekStartsOn) !== null && _ref7 !== void 0 ? _ref7 : defaultOptions.weekStartsOn) !== null && _ref6 !== void 0 ? _ref6 : (_defaultOptions$local3 = defaultOptions.locale) === null || _defaultOptions$local3 === void 0 ? void 0 : (_defaultOptions$local4 = _defaultOptions$local3.options) === null || _defaultOptions$local4 === void 0 ? void 0 : _defaultOptions$local4.weekStartsOn) !== null && _ref5 !== void 0 ? _ref5 : 0);

  // Test if weekStartsOn is between 0 and 6 _and_ is not NaN
  if (!(weekStartsOn >= 0 && weekStartsOn <= 6)) {
    throw new RangeError('weekStartsOn must be between 0 and 6 inclusively');
  }
  if (!locale.localize) {
    throw new RangeError('locale must contain localize property');
  }
  if (!locale.formatLong) {
    throw new RangeError('locale must contain formatLong property');
  }
  var originalDate = toDate(dirtyDate);
  if (!isValid(originalDate)) {
    throw new RangeError('Invalid time value');
  }

  // Convert the date in system timezone to the same date in UTC+00:00 timezone.
  // This ensures that when UTC functions will be implemented, locales will be compatible with them.
  // See an issue about UTC functions: https://github.com/date-fns/date-fns/issues/376
  var timezoneOffset = getTimezoneOffsetInMilliseconds(originalDate);
  var utcDate = subMilliseconds(originalDate, timezoneOffset);
  var formatterOptions = {
    firstWeekContainsDate: firstWeekContainsDate,
    weekStartsOn: weekStartsOn,
    locale: locale,
    _originalDate: originalDate
  };
  var result = formatStr.match(longFormattingTokensRegExp).map(function (substring) {
    var firstCharacter = substring[0];
    if (firstCharacter === 'p' || firstCharacter === 'P') {
      var longFormatter = longFormatters$1[firstCharacter];
      return longFormatter(substring, locale.formatLong);
    }
    return substring;
  }).join('').match(formattingTokensRegExp).map(function (substring) {
    // Replace two single quote characters with one single quote character
    if (substring === "''") {
      return "'";
    }
    var firstCharacter = substring[0];
    if (firstCharacter === "'") {
      return cleanEscapedString(substring);
    }
    var formatter = formatters$1[firstCharacter];
    if (formatter) {
      if (!(options !== null && options !== void 0 && options.useAdditionalWeekYearTokens) && isProtectedWeekYearToken(substring)) {
        throwProtectedError(substring, dirtyFormatStr, String(dirtyDate));
      }
      if (!(options !== null && options !== void 0 && options.useAdditionalDayOfYearTokens) && isProtectedDayOfYearToken(substring)) {
        throwProtectedError(substring, dirtyFormatStr, String(dirtyDate));
      }
      return formatter(utcDate, substring, locale.localize, formatterOptions);
    }
    if (firstCharacter.match(unescapedLatinCharacterRegExp)) {
      throw new RangeError('Format string contains an unescaped latin alphabet character `' + firstCharacter + '`');
    }
    return substring;
  }).join('');
  return result;
}
function cleanEscapedString(input) {
  var matched = input.match(escapedStringRegExp);
  if (!matched) {
    return input;
  }
  return matched[1].replace(doubleQuoteRegExp, "'");
}

var lib = {};

var uaParser_min = {exports: {}};

/* UAParser.js v1.0.35
   Copyright © 2012-2021 Faisal Salman <f@faisalman.com>
   MIT License */

(function (module, exports) {
	(function(window,undefined$1){var LIBVERSION="1.0.35",EMPTY="",UNKNOWN="?",FUNC_TYPE="function",UNDEF_TYPE="undefined",OBJ_TYPE="object",STR_TYPE="string",MAJOR="major",MODEL="model",NAME="name",TYPE="type",VENDOR="vendor",VERSION="version",ARCHITECTURE="architecture",CONSOLE="console",MOBILE="mobile",TABLET="tablet",SMARTTV="smarttv",WEARABLE="wearable",EMBEDDED="embedded",UA_MAX_LENGTH=350;var AMAZON="Amazon",APPLE="Apple",ASUS="ASUS",BLACKBERRY="BlackBerry",BROWSER="Browser",CHROME="Chrome",EDGE="Edge",FIREFOX="Firefox",GOOGLE="Google",HUAWEI="Huawei",LG="LG",MICROSOFT="Microsoft",MOTOROLA="Motorola",OPERA="Opera",SAMSUNG="Samsung",SHARP="Sharp",SONY="Sony",XIAOMI="Xiaomi",ZEBRA="Zebra",FACEBOOK="Facebook",CHROMIUM_OS="Chromium OS",MAC_OS="Mac OS";var extend=function(regexes,extensions){var mergedRegexes={};for(var i in regexes){if(extensions[i]&&extensions[i].length%2===0){mergedRegexes[i]=extensions[i].concat(regexes[i]);}else {mergedRegexes[i]=regexes[i];}}return mergedRegexes},enumerize=function(arr){var enums={};for(var i=0;i<arr.length;i++){enums[arr[i].toUpperCase()]=arr[i];}return enums},has=function(str1,str2){return typeof str1===STR_TYPE?lowerize(str2).indexOf(lowerize(str1))!==-1:false},lowerize=function(str){return str.toLowerCase()},majorize=function(version){return typeof version===STR_TYPE?version.replace(/[^\d\.]/g,EMPTY).split(".")[0]:undefined$1},trim=function(str,len){if(typeof str===STR_TYPE){str=str.replace(/^\s\s*/,EMPTY);return typeof len===UNDEF_TYPE?str:str.substring(0,UA_MAX_LENGTH)}};var rgxMapper=function(ua,arrays){var i=0,j,k,p,q,matches,match;while(i<arrays.length&&!matches){var regex=arrays[i],props=arrays[i+1];j=k=0;while(j<regex.length&&!matches){if(!regex[j]){break}matches=regex[j++].exec(ua);if(!!matches){for(p=0;p<props.length;p++){match=matches[++k];q=props[p];if(typeof q===OBJ_TYPE&&q.length>0){if(q.length===2){if(typeof q[1]==FUNC_TYPE){this[q[0]]=q[1].call(this,match);}else {this[q[0]]=q[1];}}else if(q.length===3){if(typeof q[1]===FUNC_TYPE&&!(q[1].exec&&q[1].test)){this[q[0]]=match?q[1].call(this,match,q[2]):undefined$1;}else {this[q[0]]=match?match.replace(q[1],q[2]):undefined$1;}}else if(q.length===4){this[q[0]]=match?q[3].call(this,match.replace(q[1],q[2])):undefined$1;}}else {this[q]=match?match:undefined$1;}}}}i+=2;}},strMapper=function(str,map){for(var i in map){if(typeof map[i]===OBJ_TYPE&&map[i].length>0){for(var j=0;j<map[i].length;j++){if(has(map[i][j],str)){return i===UNKNOWN?undefined$1:i}}}else if(has(map[i],str)){return i===UNKNOWN?undefined$1:i}}return str};var oldSafariMap={"1.0":"/8",1.2:"/1",1.3:"/3","2.0":"/412","2.0.2":"/416","2.0.3":"/417","2.0.4":"/419","?":"/"},windowsVersionMap={ME:"4.90","NT 3.11":"NT3.51","NT 4.0":"NT4.0",2e3:"NT 5.0",XP:["NT 5.1","NT 5.2"],Vista:"NT 6.0",7:"NT 6.1",8:"NT 6.2",8.1:"NT 6.3",10:["NT 6.4","NT 10.0"],RT:"ARM"};var regexes={browser:[[/\b(?:crmo|crios)\/([\w\.]+)/i],[VERSION,[NAME,"Chrome"]],[/edg(?:e|ios|a)?\/([\w\.]+)/i],[VERSION,[NAME,"Edge"]],[/(opera mini)\/([-\w\.]+)/i,/(opera [mobiletab]{3,6})\b.+version\/([-\w\.]+)/i,/(opera)(?:.+version\/|[\/ ]+)([\w\.]+)/i],[NAME,VERSION],[/opios[\/ ]+([\w\.]+)/i],[VERSION,[NAME,OPERA+" Mini"]],[/\bopr\/([\w\.]+)/i],[VERSION,[NAME,OPERA]],[/(kindle)\/([\w\.]+)/i,/(lunascape|maxthon|netfront|jasmine|blazer)[\/ ]?([\w\.]*)/i,/(avant |iemobile|slim)(?:browser)?[\/ ]?([\w\.]*)/i,/(ba?idubrowser)[\/ ]?([\w\.]+)/i,/(?:ms|\()(ie) ([\w\.]+)/i,/(flock|rockmelt|midori|epiphany|silk|skyfire|bolt|iron|vivaldi|iridium|phantomjs|bowser|quark|qupzilla|falkon|rekonq|puffin|brave|whale(?!.+naver)|qqbrowserlite|qq|duckduckgo)\/([-\w\.]+)/i,/(heytap|ovi)browser\/([\d\.]+)/i,/(weibo)__([\d\.]+)/i],[NAME,VERSION],[/(?:\buc? ?browser|(?:juc.+)ucweb)[\/ ]?([\w\.]+)/i],[VERSION,[NAME,"UC"+BROWSER]],[/microm.+\bqbcore\/([\w\.]+)/i,/\bqbcore\/([\w\.]+).+microm/i],[VERSION,[NAME,"WeChat(Win) Desktop"]],[/micromessenger\/([\w\.]+)/i],[VERSION,[NAME,"WeChat"]],[/konqueror\/([\w\.]+)/i],[VERSION,[NAME,"Konqueror"]],[/trident.+rv[: ]([\w\.]{1,9})\b.+like gecko/i],[VERSION,[NAME,"IE"]],[/ya(?:search)?browser\/([\w\.]+)/i],[VERSION,[NAME,"Yandex"]],[/(avast|avg)\/([\w\.]+)/i],[[NAME,/(.+)/,"$1 Secure "+BROWSER],VERSION],[/\bfocus\/([\w\.]+)/i],[VERSION,[NAME,FIREFOX+" Focus"]],[/\bopt\/([\w\.]+)/i],[VERSION,[NAME,OPERA+" Touch"]],[/coc_coc\w+\/([\w\.]+)/i],[VERSION,[NAME,"Coc Coc"]],[/dolfin\/([\w\.]+)/i],[VERSION,[NAME,"Dolphin"]],[/coast\/([\w\.]+)/i],[VERSION,[NAME,OPERA+" Coast"]],[/miuibrowser\/([\w\.]+)/i],[VERSION,[NAME,"MIUI "+BROWSER]],[/fxios\/([-\w\.]+)/i],[VERSION,[NAME,FIREFOX]],[/\bqihu|(qi?ho?o?|360)browser/i],[[NAME,"360 "+BROWSER]],[/(oculus|samsung|sailfish|huawei)browser\/([\w\.]+)/i],[[NAME,/(.+)/,"$1 "+BROWSER],VERSION],[/(comodo_dragon)\/([\w\.]+)/i],[[NAME,/_/g," "],VERSION],[/(electron)\/([\w\.]+) safari/i,/(tesla)(?: qtcarbrowser|\/(20\d\d\.[-\w\.]+))/i,/m?(qqbrowser|baiduboxapp|2345Explorer)[\/ ]?([\w\.]+)/i],[NAME,VERSION],[/(metasr)[\/ ]?([\w\.]+)/i,/(lbbrowser)/i,/\[(linkedin)app\]/i],[NAME],[/((?:fban\/fbios|fb_iab\/fb4a)(?!.+fbav)|;fbav\/([\w\.]+);)/i],[[NAME,FACEBOOK],VERSION],[/(kakao(?:talk|story))[\/ ]([\w\.]+)/i,/(naver)\(.*?(\d+\.[\w\.]+).*\)/i,/safari (line)\/([\w\.]+)/i,/\b(line)\/([\w\.]+)\/iab/i,/(chromium|instagram)[\/ ]([-\w\.]+)/i],[NAME,VERSION],[/\bgsa\/([\w\.]+) .*safari\//i],[VERSION,[NAME,"GSA"]],[/musical_ly(?:.+app_?version\/|_)([\w\.]+)/i],[VERSION,[NAME,"TikTok"]],[/headlesschrome(?:\/([\w\.]+)| )/i],[VERSION,[NAME,CHROME+" Headless"]],[/ wv\).+(chrome)\/([\w\.]+)/i],[[NAME,CHROME+" WebView"],VERSION],[/droid.+ version\/([\w\.]+)\b.+(?:mobile safari|safari)/i],[VERSION,[NAME,"Android "+BROWSER]],[/(chrome|omniweb|arora|[tizenoka]{5} ?browser)\/v?([\w\.]+)/i],[NAME,VERSION],[/version\/([\w\.\,]+) .*mobile\/\w+ (safari)/i],[VERSION,[NAME,"Mobile Safari"]],[/version\/([\w(\.|\,)]+) .*(mobile ?safari|safari)/i],[VERSION,NAME],[/webkit.+?(mobile ?safari|safari)(\/[\w\.]+)/i],[NAME,[VERSION,strMapper,oldSafariMap]],[/(webkit|khtml)\/([\w\.]+)/i],[NAME,VERSION],[/(navigator|netscape\d?)\/([-\w\.]+)/i],[[NAME,"Netscape"],VERSION],[/mobile vr; rv:([\w\.]+)\).+firefox/i],[VERSION,[NAME,FIREFOX+" Reality"]],[/ekiohf.+(flow)\/([\w\.]+)/i,/(swiftfox)/i,/(icedragon|iceweasel|camino|chimera|fennec|maemo browser|minimo|conkeror|klar)[\/ ]?([\w\.\+]+)/i,/(seamonkey|k-meleon|icecat|iceape|firebird|phoenix|palemoon|basilisk|waterfox)\/([-\w\.]+)$/i,/(firefox)\/([\w\.]+)/i,/(mozilla)\/([\w\.]+) .+rv\:.+gecko\/\d+/i,/(polaris|lynx|dillo|icab|doris|amaya|w3m|netsurf|sleipnir|obigo|mosaic|(?:go|ice|up)[\. ]?browser)[-\/ ]?v?([\w\.]+)/i,/(links) \(([\w\.]+)/i,/panasonic;(viera)/i],[NAME,VERSION],[/(cobalt)\/([\w\.]+)/i],[NAME,[VERSION,/master.|lts./,""]]],cpu:[[/(?:(amd|x(?:(?:86|64)[-_])?|wow|win)64)[;\)]/i],[[ARCHITECTURE,"amd64"]],[/(ia32(?=;))/i],[[ARCHITECTURE,lowerize]],[/((?:i[346]|x)86)[;\)]/i],[[ARCHITECTURE,"ia32"]],[/\b(aarch64|arm(v?8e?l?|_?64))\b/i],[[ARCHITECTURE,"arm64"]],[/\b(arm(?:v[67])?ht?n?[fl]p?)\b/i],[[ARCHITECTURE,"armhf"]],[/windows (ce|mobile); ppc;/i],[[ARCHITECTURE,"arm"]],[/((?:ppc|powerpc)(?:64)?)(?: mac|;|\))/i],[[ARCHITECTURE,/ower/,EMPTY,lowerize]],[/(sun4\w)[;\)]/i],[[ARCHITECTURE,"sparc"]],[/((?:avr32|ia64(?=;))|68k(?=\))|\barm(?=v(?:[1-7]|[5-7]1)l?|;|eabi)|(?=atmel )avr|(?:irix|mips|sparc)(?:64)?\b|pa-risc)/i],[[ARCHITECTURE,lowerize]]],device:[[/\b(sch-i[89]0\d|shw-m380s|sm-[ptx]\w{2,4}|gt-[pn]\d{2,4}|sgh-t8[56]9|nexus 10)/i],[MODEL,[VENDOR,SAMSUNG],[TYPE,TABLET]],[/\b((?:s[cgp]h|gt|sm)-\w+|sc[g-]?[\d]+a?|galaxy nexus)/i,/samsung[- ]([-\w]+)/i,/sec-(sgh\w+)/i],[MODEL,[VENDOR,SAMSUNG],[TYPE,MOBILE]],[/(?:\/|\()(ip(?:hone|od)[\w, ]*)(?:\/|;)/i],[MODEL,[VENDOR,APPLE],[TYPE,MOBILE]],[/\((ipad);[-\w\),; ]+apple/i,/applecoremedia\/[\w\.]+ \((ipad)/i,/\b(ipad)\d\d?,\d\d?[;\]].+ios/i],[MODEL,[VENDOR,APPLE],[TYPE,TABLET]],[/(macintosh);/i],[MODEL,[VENDOR,APPLE]],[/\b(sh-?[altvz]?\d\d[a-ekm]?)/i],[MODEL,[VENDOR,SHARP],[TYPE,MOBILE]],[/\b((?:ag[rs][23]?|bah2?|sht?|btv)-a?[lw]\d{2})\b(?!.+d\/s)/i],[MODEL,[VENDOR,HUAWEI],[TYPE,TABLET]],[/(?:huawei|honor)([-\w ]+)[;\)]/i,/\b(nexus 6p|\w{2,4}e?-[atu]?[ln][\dx][012359c][adn]?)\b(?!.+d\/s)/i],[MODEL,[VENDOR,HUAWEI],[TYPE,MOBILE]],[/\b(poco[\w ]+)(?: bui|\))/i,/\b; (\w+) build\/hm\1/i,/\b(hm[-_ ]?note?[_ ]?(?:\d\w)?) bui/i,/\b(redmi[\-_ ]?(?:note|k)?[\w_ ]+)(?: bui|\))/i,/\b(mi[-_ ]?(?:a\d|one|one[_ ]plus|note lte|max|cc)?[_ ]?(?:\d?\w?)[_ ]?(?:plus|se|lite)?)(?: bui|\))/i],[[MODEL,/_/g," "],[VENDOR,XIAOMI],[TYPE,MOBILE]],[/\b(mi[-_ ]?(?:pad)(?:[\w_ ]+))(?: bui|\))/i],[[MODEL,/_/g," "],[VENDOR,XIAOMI],[TYPE,TABLET]],[/; (\w+) bui.+ oppo/i,/\b(cph[12]\d{3}|p(?:af|c[al]|d\w|e[ar])[mt]\d0|x9007|a101op)\b/i],[MODEL,[VENDOR,"OPPO"],[TYPE,MOBILE]],[/vivo (\w+)(?: bui|\))/i,/\b(v[12]\d{3}\w?[at])(?: bui|;)/i],[MODEL,[VENDOR,"Vivo"],[TYPE,MOBILE]],[/\b(rmx[12]\d{3})(?: bui|;|\))/i],[MODEL,[VENDOR,"Realme"],[TYPE,MOBILE]],[/\b(milestone|droid(?:[2-4x]| (?:bionic|x2|pro|razr))?:?( 4g)?)\b[\w ]+build\//i,/\bmot(?:orola)?[- ](\w*)/i,/((?:moto[\w\(\) ]+|xt\d{3,4}|nexus 6)(?= bui|\)))/i],[MODEL,[VENDOR,MOTOROLA],[TYPE,MOBILE]],[/\b(mz60\d|xoom[2 ]{0,2}) build\//i],[MODEL,[VENDOR,MOTOROLA],[TYPE,TABLET]],[/((?=lg)?[vl]k\-?\d{3}) bui| 3\.[-\w; ]{10}lg?-([06cv9]{3,4})/i],[MODEL,[VENDOR,LG],[TYPE,TABLET]],[/(lm(?:-?f100[nv]?|-[\w\.]+)(?= bui|\))|nexus [45])/i,/\blg[-e;\/ ]+((?!browser|netcast|android tv)\w+)/i,/\blg-?([\d\w]+) bui/i],[MODEL,[VENDOR,LG],[TYPE,MOBILE]],[/(ideatab[-\w ]+)/i,/lenovo ?(s[56]000[-\w]+|tab(?:[\w ]+)|yt[-\d\w]{6}|tb[-\d\w]{6})/i],[MODEL,[VENDOR,"Lenovo"],[TYPE,TABLET]],[/(?:maemo|nokia).*(n900|lumia \d+)/i,/nokia[-_ ]?([-\w\.]*)/i],[[MODEL,/_/g," "],[VENDOR,"Nokia"],[TYPE,MOBILE]],[/(pixel c)\b/i],[MODEL,[VENDOR,GOOGLE],[TYPE,TABLET]],[/droid.+; (pixel[\daxl ]{0,6})(?: bui|\))/i],[MODEL,[VENDOR,GOOGLE],[TYPE,MOBILE]],[/droid.+ (a?\d[0-2]{2}so|[c-g]\d{4}|so[-gl]\w+|xq-a\w[4-7][12])(?= bui|\).+chrome\/(?![1-6]{0,1}\d\.))/i],[MODEL,[VENDOR,SONY],[TYPE,MOBILE]],[/sony tablet [ps]/i,/\b(?:sony)?sgp\w+(?: bui|\))/i],[[MODEL,"Xperia Tablet"],[VENDOR,SONY],[TYPE,TABLET]],[/ (kb2005|in20[12]5|be20[12][59])\b/i,/(?:one)?(?:plus)? (a\d0\d\d)(?: b|\))/i],[MODEL,[VENDOR,"OnePlus"],[TYPE,MOBILE]],[/(alexa)webm/i,/(kf[a-z]{2}wi|aeo[c-r]{2})( bui|\))/i,/(kf[a-z]+)( bui|\)).+silk\//i],[MODEL,[VENDOR,AMAZON],[TYPE,TABLET]],[/((?:sd|kf)[0349hijorstuw]+)( bui|\)).+silk\//i],[[MODEL,/(.+)/g,"Fire Phone $1"],[VENDOR,AMAZON],[TYPE,MOBILE]],[/(playbook);[-\w\),; ]+(rim)/i],[MODEL,VENDOR,[TYPE,TABLET]],[/\b((?:bb[a-f]|st[hv])100-\d)/i,/\(bb10; (\w+)/i],[MODEL,[VENDOR,BLACKBERRY],[TYPE,MOBILE]],[/(?:\b|asus_)(transfo[prime ]{4,10} \w+|eeepc|slider \w+|nexus 7|padfone|p00[cj])/i],[MODEL,[VENDOR,ASUS],[TYPE,TABLET]],[/ (z[bes]6[027][012][km][ls]|zenfone \d\w?)\b/i],[MODEL,[VENDOR,ASUS],[TYPE,MOBILE]],[/(nexus 9)/i],[MODEL,[VENDOR,"HTC"],[TYPE,TABLET]],[/(htc)[-;_ ]{1,2}([\w ]+(?=\)| bui)|\w+)/i,/(zte)[- ]([\w ]+?)(?: bui|\/|\))/i,/(alcatel|geeksphone|nexian|panasonic(?!(?:;|\.))|sony(?!-bra))[-_ ]?([-\w]*)/i],[VENDOR,[MODEL,/_/g," "],[TYPE,MOBILE]],[/droid.+; ([ab][1-7]-?[0178a]\d\d?)/i],[MODEL,[VENDOR,"Acer"],[TYPE,TABLET]],[/droid.+; (m[1-5] note) bui/i,/\bmz-([-\w]{2,})/i],[MODEL,[VENDOR,"Meizu"],[TYPE,MOBILE]],[/(blackberry|benq|palm(?=\-)|sonyericsson|acer|asus|dell|meizu|motorola|polytron)[-_ ]?([-\w]*)/i,/(hp) ([\w ]+\w)/i,/(asus)-?(\w+)/i,/(microsoft); (lumia[\w ]+)/i,/(lenovo)[-_ ]?([-\w]+)/i,/(jolla)/i,/(oppo) ?([\w ]+) bui/i],[VENDOR,MODEL,[TYPE,MOBILE]],[/(kobo)\s(ereader|touch)/i,/(archos) (gamepad2?)/i,/(hp).+(touchpad(?!.+tablet)|tablet)/i,/(kindle)\/([\w\.]+)/i,/(nook)[\w ]+build\/(\w+)/i,/(dell) (strea[kpr\d ]*[\dko])/i,/(le[- ]+pan)[- ]+(\w{1,9}) bui/i,/(trinity)[- ]*(t\d{3}) bui/i,/(gigaset)[- ]+(q\w{1,9}) bui/i,/(vodafone) ([\w ]+)(?:\)| bui)/i],[VENDOR,MODEL,[TYPE,TABLET]],[/(surface duo)/i],[MODEL,[VENDOR,MICROSOFT],[TYPE,TABLET]],[/droid [\d\.]+; (fp\du?)(?: b|\))/i],[MODEL,[VENDOR,"Fairphone"],[TYPE,MOBILE]],[/(u304aa)/i],[MODEL,[VENDOR,"AT&T"],[TYPE,MOBILE]],[/\bsie-(\w*)/i],[MODEL,[VENDOR,"Siemens"],[TYPE,MOBILE]],[/\b(rct\w+) b/i],[MODEL,[VENDOR,"RCA"],[TYPE,TABLET]],[/\b(venue[\d ]{2,7}) b/i],[MODEL,[VENDOR,"Dell"],[TYPE,TABLET]],[/\b(q(?:mv|ta)\w+) b/i],[MODEL,[VENDOR,"Verizon"],[TYPE,TABLET]],[/\b(?:barnes[& ]+noble |bn[rt])([\w\+ ]*) b/i],[MODEL,[VENDOR,"Barnes & Noble"],[TYPE,TABLET]],[/\b(tm\d{3}\w+) b/i],[MODEL,[VENDOR,"NuVision"],[TYPE,TABLET]],[/\b(k88) b/i],[MODEL,[VENDOR,"ZTE"],[TYPE,TABLET]],[/\b(nx\d{3}j) b/i],[MODEL,[VENDOR,"ZTE"],[TYPE,MOBILE]],[/\b(gen\d{3}) b.+49h/i],[MODEL,[VENDOR,"Swiss"],[TYPE,MOBILE]],[/\b(zur\d{3}) b/i],[MODEL,[VENDOR,"Swiss"],[TYPE,TABLET]],[/\b((zeki)?tb.*\b) b/i],[MODEL,[VENDOR,"Zeki"],[TYPE,TABLET]],[/\b([yr]\d{2}) b/i,/\b(dragon[- ]+touch |dt)(\w{5}) b/i],[[VENDOR,"Dragon Touch"],MODEL,[TYPE,TABLET]],[/\b(ns-?\w{0,9}) b/i],[MODEL,[VENDOR,"Insignia"],[TYPE,TABLET]],[/\b((nxa|next)-?\w{0,9}) b/i],[MODEL,[VENDOR,"NextBook"],[TYPE,TABLET]],[/\b(xtreme\_)?(v(1[045]|2[015]|[3469]0|7[05])) b/i],[[VENDOR,"Voice"],MODEL,[TYPE,MOBILE]],[/\b(lvtel\-)?(v1[12]) b/i],[[VENDOR,"LvTel"],MODEL,[TYPE,MOBILE]],[/\b(ph-1) /i],[MODEL,[VENDOR,"Essential"],[TYPE,MOBILE]],[/\b(v(100md|700na|7011|917g).*\b) b/i],[MODEL,[VENDOR,"Envizen"],[TYPE,TABLET]],[/\b(trio[-\w\. ]+) b/i],[MODEL,[VENDOR,"MachSpeed"],[TYPE,TABLET]],[/\btu_(1491) b/i],[MODEL,[VENDOR,"Rotor"],[TYPE,TABLET]],[/(shield[\w ]+) b/i],[MODEL,[VENDOR,"Nvidia"],[TYPE,TABLET]],[/(sprint) (\w+)/i],[VENDOR,MODEL,[TYPE,MOBILE]],[/(kin\.[onetw]{3})/i],[[MODEL,/\./g," "],[VENDOR,MICROSOFT],[TYPE,MOBILE]],[/droid.+; (cc6666?|et5[16]|mc[239][23]x?|vc8[03]x?)\)/i],[MODEL,[VENDOR,ZEBRA],[TYPE,TABLET]],[/droid.+; (ec30|ps20|tc[2-8]\d[kx])\)/i],[MODEL,[VENDOR,ZEBRA],[TYPE,MOBILE]],[/smart-tv.+(samsung)/i],[VENDOR,[TYPE,SMARTTV]],[/hbbtv.+maple;(\d+)/i],[[MODEL,/^/,"SmartTV"],[VENDOR,SAMSUNG],[TYPE,SMARTTV]],[/(nux; netcast.+smarttv|lg (netcast\.tv-201\d|android tv))/i],[[VENDOR,LG],[TYPE,SMARTTV]],[/(apple) ?tv/i],[VENDOR,[MODEL,APPLE+" TV"],[TYPE,SMARTTV]],[/crkey/i],[[MODEL,CHROME+"cast"],[VENDOR,GOOGLE],[TYPE,SMARTTV]],[/droid.+aft(\w)( bui|\))/i],[MODEL,[VENDOR,AMAZON],[TYPE,SMARTTV]],[/\(dtv[\);].+(aquos)/i,/(aquos-tv[\w ]+)\)/i],[MODEL,[VENDOR,SHARP],[TYPE,SMARTTV]],[/(bravia[\w ]+)( bui|\))/i],[MODEL,[VENDOR,SONY],[TYPE,SMARTTV]],[/(mitv-\w{5}) bui/i],[MODEL,[VENDOR,XIAOMI],[TYPE,SMARTTV]],[/Hbbtv.*(technisat) (.*);/i],[VENDOR,MODEL,[TYPE,SMARTTV]],[/\b(roku)[\dx]*[\)\/]((?:dvp-)?[\d\.]*)/i,/hbbtv\/\d+\.\d+\.\d+ +\([\w\+ ]*; *([\w\d][^;]*);([^;]*)/i],[[VENDOR,trim],[MODEL,trim],[TYPE,SMARTTV]],[/\b(android tv|smart[- ]?tv|opera tv|tv; rv:)\b/i],[[TYPE,SMARTTV]],[/(ouya)/i,/(nintendo) ([wids3utch]+)/i],[VENDOR,MODEL,[TYPE,CONSOLE]],[/droid.+; (shield) bui/i],[MODEL,[VENDOR,"Nvidia"],[TYPE,CONSOLE]],[/(playstation [345portablevi]+)/i],[MODEL,[VENDOR,SONY],[TYPE,CONSOLE]],[/\b(xbox(?: one)?(?!; xbox))[\); ]/i],[MODEL,[VENDOR,MICROSOFT],[TYPE,CONSOLE]],[/((pebble))app/i],[VENDOR,MODEL,[TYPE,WEARABLE]],[/(watch)(?: ?os[,\/]|\d,\d\/)[\d\.]+/i],[MODEL,[VENDOR,APPLE],[TYPE,WEARABLE]],[/droid.+; (glass) \d/i],[MODEL,[VENDOR,GOOGLE],[TYPE,WEARABLE]],[/droid.+; (wt63?0{2,3})\)/i],[MODEL,[VENDOR,ZEBRA],[TYPE,WEARABLE]],[/(quest( 2| pro)?)/i],[MODEL,[VENDOR,FACEBOOK],[TYPE,WEARABLE]],[/(tesla)(?: qtcarbrowser|\/[-\w\.]+)/i],[VENDOR,[TYPE,EMBEDDED]],[/(aeobc)\b/i],[MODEL,[VENDOR,AMAZON],[TYPE,EMBEDDED]],[/droid .+?; ([^;]+?)(?: bui|\) applew).+? mobile safari/i],[MODEL,[TYPE,MOBILE]],[/droid .+?; ([^;]+?)(?: bui|\) applew).+?(?! mobile) safari/i],[MODEL,[TYPE,TABLET]],[/\b((tablet|tab)[;\/]|focus\/\d(?!.+mobile))/i],[[TYPE,TABLET]],[/(phone|mobile(?:[;\/]| [ \w\/\.]*safari)|pda(?=.+windows ce))/i],[[TYPE,MOBILE]],[/(android[-\w\. ]{0,9});.+buil/i],[MODEL,[VENDOR,"Generic"]]],engine:[[/windows.+ edge\/([\w\.]+)/i],[VERSION,[NAME,EDGE+"HTML"]],[/webkit\/537\.36.+chrome\/(?!27)([\w\.]+)/i],[VERSION,[NAME,"Blink"]],[/(presto)\/([\w\.]+)/i,/(webkit|trident|netfront|netsurf|amaya|lynx|w3m|goanna)\/([\w\.]+)/i,/ekioh(flow)\/([\w\.]+)/i,/(khtml|tasman|links)[\/ ]\(?([\w\.]+)/i,/(icab)[\/ ]([23]\.[\d\.]+)/i,/\b(libweb)/i],[NAME,VERSION],[/rv\:([\w\.]{1,9})\b.+(gecko)/i],[VERSION,NAME]],os:[[/microsoft (windows) (vista|xp)/i],[NAME,VERSION],[/(windows) nt 6\.2; (arm)/i,/(windows (?:phone(?: os)?|mobile))[\/ ]?([\d\.\w ]*)/i,/(windows)[\/ ]?([ntce\d\. ]+\w)(?!.+xbox)/i],[NAME,[VERSION,strMapper,windowsVersionMap]],[/(win(?=3|9|n)|win 9x )([nt\d\.]+)/i],[[NAME,"Windows"],[VERSION,strMapper,windowsVersionMap]],[/ip[honead]{2,4}\b(?:.*os ([\w]+) like mac|; opera)/i,/ios;fbsv\/([\d\.]+)/i,/cfnetwork\/.+darwin/i],[[VERSION,/_/g,"."],[NAME,"iOS"]],[/(mac os x) ?([\w\. ]*)/i,/(macintosh|mac_powerpc\b)(?!.+haiku)/i],[[NAME,MAC_OS],[VERSION,/_/g,"."]],[/droid ([\w\.]+)\b.+(android[- ]x86|harmonyos)/i],[VERSION,NAME],[/(android|webos|qnx|bada|rim tablet os|maemo|meego|sailfish)[-\/ ]?([\w\.]*)/i,/(blackberry)\w*\/([\w\.]*)/i,/(tizen|kaios)[\/ ]([\w\.]+)/i,/\((series40);/i],[NAME,VERSION],[/\(bb(10);/i],[VERSION,[NAME,BLACKBERRY]],[/(?:symbian ?os|symbos|s60(?=;)|series60)[-\/ ]?([\w\.]*)/i],[VERSION,[NAME,"Symbian"]],[/mozilla\/[\d\.]+ \((?:mobile|tablet|tv|mobile; [\w ]+); rv:.+ gecko\/([\w\.]+)/i],[VERSION,[NAME,FIREFOX+" OS"]],[/web0s;.+rt(tv)/i,/\b(?:hp)?wos(?:browser)?\/([\w\.]+)/i],[VERSION,[NAME,"webOS"]],[/watch(?: ?os[,\/]|\d,\d\/)([\d\.]+)/i],[VERSION,[NAME,"watchOS"]],[/crkey\/([\d\.]+)/i],[VERSION,[NAME,CHROME+"cast"]],[/(cros) [\w]+(?:\)| ([\w\.]+)\b)/i],[[NAME,CHROMIUM_OS],VERSION],[/panasonic;(viera)/i,/(netrange)mmh/i,/(nettv)\/(\d+\.[\w\.]+)/i,/(nintendo|playstation) ([wids345portablevuch]+)/i,/(xbox); +xbox ([^\);]+)/i,/\b(joli|palm)\b ?(?:os)?\/?([\w\.]*)/i,/(mint)[\/\(\) ]?(\w*)/i,/(mageia|vectorlinux)[; ]/i,/([kxln]?ubuntu|debian|suse|opensuse|gentoo|arch(?= linux)|slackware|fedora|mandriva|centos|pclinuxos|red ?hat|zenwalk|linpus|raspbian|plan 9|minix|risc os|contiki|deepin|manjaro|elementary os|sabayon|linspire)(?: gnu\/linux)?(?: enterprise)?(?:[- ]linux)?(?:-gnu)?[-\/ ]?(?!chrom|package)([-\w\.]*)/i,/(hurd|linux) ?([\w\.]*)/i,/(gnu) ?([\w\.]*)/i,/\b([-frentopcghs]{0,5}bsd|dragonfly)[\/ ]?(?!amd|[ix346]{1,2}86)([\w\.]*)/i,/(haiku) (\w+)/i],[NAME,VERSION],[/(sunos) ?([\w\.\d]*)/i],[[NAME,"Solaris"],VERSION],[/((?:open)?solaris)[-\/ ]?([\w\.]*)/i,/(aix) ((\d)(?=\.|\)| )[\w\.])*/i,/\b(beos|os\/2|amigaos|morphos|openvms|fuchsia|hp-ux|serenityos)/i,/(unix) ?([\w\.]*)/i],[NAME,VERSION]]};var UAParser=function(ua,extensions){if(typeof ua===OBJ_TYPE){extensions=ua;ua=undefined$1;}if(!(this instanceof UAParser)){return new UAParser(ua,extensions).getResult()}var _navigator=typeof window!==UNDEF_TYPE&&window.navigator?window.navigator:undefined$1;var _ua=ua||(_navigator&&_navigator.userAgent?_navigator.userAgent:EMPTY);var _uach=_navigator&&_navigator.userAgentData?_navigator.userAgentData:undefined$1;var _rgxmap=extensions?extend(regexes,extensions):regexes;var _isSelfNav=_navigator&&_navigator.userAgent==_ua;this.getBrowser=function(){var _browser={};_browser[NAME]=undefined$1;_browser[VERSION]=undefined$1;rgxMapper.call(_browser,_ua,_rgxmap.browser);_browser[MAJOR]=majorize(_browser[VERSION]);if(_isSelfNav&&_navigator&&_navigator.brave&&typeof _navigator.brave.isBrave==FUNC_TYPE){_browser[NAME]="Brave";}return _browser};this.getCPU=function(){var _cpu={};_cpu[ARCHITECTURE]=undefined$1;rgxMapper.call(_cpu,_ua,_rgxmap.cpu);return _cpu};this.getDevice=function(){var _device={};_device[VENDOR]=undefined$1;_device[MODEL]=undefined$1;_device[TYPE]=undefined$1;rgxMapper.call(_device,_ua,_rgxmap.device);if(_isSelfNav&&!_device[TYPE]&&_uach&&_uach.mobile){_device[TYPE]=MOBILE;}if(_isSelfNav&&_device[MODEL]=="Macintosh"&&_navigator&&typeof _navigator.standalone!==UNDEF_TYPE&&_navigator.maxTouchPoints&&_navigator.maxTouchPoints>2){_device[MODEL]="iPad";_device[TYPE]=TABLET;}return _device};this.getEngine=function(){var _engine={};_engine[NAME]=undefined$1;_engine[VERSION]=undefined$1;rgxMapper.call(_engine,_ua,_rgxmap.engine);return _engine};this.getOS=function(){var _os={};_os[NAME]=undefined$1;_os[VERSION]=undefined$1;rgxMapper.call(_os,_ua,_rgxmap.os);if(_isSelfNav&&!_os[NAME]&&_uach&&_uach.platform!="Unknown"){_os[NAME]=_uach.platform.replace(/chrome os/i,CHROMIUM_OS).replace(/macos/i,MAC_OS);}return _os};this.getResult=function(){return {ua:this.getUA(),browser:this.getBrowser(),engine:this.getEngine(),os:this.getOS(),device:this.getDevice(),cpu:this.getCPU()}};this.getUA=function(){return _ua};this.setUA=function(ua){_ua=typeof ua===STR_TYPE&&ua.length>UA_MAX_LENGTH?trim(ua,UA_MAX_LENGTH):ua;return this};this.setUA(_ua);return this};UAParser.VERSION=LIBVERSION;UAParser.BROWSER=enumerize([NAME,VERSION,MAJOR]);UAParser.CPU=enumerize([ARCHITECTURE]);UAParser.DEVICE=enumerize([MODEL,VENDOR,TYPE,CONSOLE,MOBILE,SMARTTV,TABLET,WEARABLE,EMBEDDED]);UAParser.ENGINE=UAParser.OS=enumerize([NAME,VERSION]);{if(module.exports){exports=module.exports=UAParser;}exports.UAParser=UAParser;}var $=typeof window!==UNDEF_TYPE&&(window.jQuery||window.Zepto);if($&&!$.ua){var parser=new UAParser;$.ua=parser.getResult();$.ua.get=function(){return parser.getUA()};$.ua.set=function(ua){parser.setUA(ua);var result=parser.getResult();for(var prop in result){$.ua[prop]=result[prop];}};}})(typeof window==="object"?window:commonjsGlobal); 
} (uaParser_min, uaParser_min.exports));

var uaParser_minExports = uaParser_min.exports;

Object.defineProperty(lib, '__esModule', { value: true });

function _interopDefault$1 (ex) { return (ex && (typeof ex === 'object') && 'default' in ex) ? ex['default'] : ex; }

var React = React$1;
var React__default = _interopDefault$1(React);

var UAParser = uaParser_minExports;

var ClientUAInstance = new UAParser();
var browser = ClientUAInstance.getBrowser();
var cpu = ClientUAInstance.getCPU();
var device = ClientUAInstance.getDevice();
var engine = ClientUAInstance.getEngine();
var os = ClientUAInstance.getOS();
var ua = ClientUAInstance.getUA();
var setUa = function setUa(userAgentString) {
  return ClientUAInstance.setUA(userAgentString);
};
var parseUserAgent = function parseUserAgent(userAgent) {
  if (!userAgent) {
    console.error('No userAgent string was provided');
    return;
  }

  var UserAgentInstance = new UAParser(userAgent);
  return {
    UA: UserAgentInstance,
    browser: UserAgentInstance.getBrowser(),
    cpu: UserAgentInstance.getCPU(),
    device: UserAgentInstance.getDevice(),
    engine: UserAgentInstance.getEngine(),
    os: UserAgentInstance.getOS(),
    ua: UserAgentInstance.getUA(),
    setUserAgent: function setUserAgent(userAgentString) {
      return UserAgentInstance.setUA(userAgentString);
    }
  };
};

var UAHelper = /*#__PURE__*/Object.freeze({
  ClientUAInstance: ClientUAInstance,
  browser: browser,
  cpu: cpu,
  device: device,
  engine: engine,
  os: os,
  ua: ua,
  setUa: setUa,
  parseUserAgent: parseUserAgent
});

function ownKeys(object, enumerableOnly) {
  var keys = Object.keys(object);

  if (Object.getOwnPropertySymbols) {
    var symbols = Object.getOwnPropertySymbols(object);

    if (enumerableOnly) {
      symbols = symbols.filter(function (sym) {
        return Object.getOwnPropertyDescriptor(object, sym).enumerable;
      });
    }

    keys.push.apply(keys, symbols);
  }

  return keys;
}

function _objectSpread2(target) {
  for (var i = 1; i < arguments.length; i++) {
    var source = arguments[i] != null ? arguments[i] : {};

    if (i % 2) {
      ownKeys(Object(source), true).forEach(function (key) {
        _defineProperty(target, key, source[key]);
      });
    } else if (Object.getOwnPropertyDescriptors) {
      Object.defineProperties(target, Object.getOwnPropertyDescriptors(source));
    } else {
      ownKeys(Object(source)).forEach(function (key) {
        Object.defineProperty(target, key, Object.getOwnPropertyDescriptor(source, key));
      });
    }
  }

  return target;
}

function _typeof(obj) {
  "@babel/helpers - typeof";

  if (typeof Symbol === "function" && typeof Symbol.iterator === "symbol") {
    _typeof = function (obj) {
      return typeof obj;
    };
  } else {
    _typeof = function (obj) {
      return obj && typeof Symbol === "function" && obj.constructor === Symbol && obj !== Symbol.prototype ? "symbol" : typeof obj;
    };
  }

  return _typeof(obj);
}

function _classCallCheck(instance, Constructor) {
  if (!(instance instanceof Constructor)) {
    throw new TypeError("Cannot call a class as a function");
  }
}

function _defineProperties(target, props) {
  for (var i = 0; i < props.length; i++) {
    var descriptor = props[i];
    descriptor.enumerable = descriptor.enumerable || false;
    descriptor.configurable = true;
    if ("value" in descriptor) descriptor.writable = true;
    Object.defineProperty(target, descriptor.key, descriptor);
  }
}

function _createClass(Constructor, protoProps, staticProps) {
  if (protoProps) _defineProperties(Constructor.prototype, protoProps);
  if (staticProps) _defineProperties(Constructor, staticProps);
  return Constructor;
}

function _defineProperty(obj, key, value) {
  if (key in obj) {
    Object.defineProperty(obj, key, {
      value: value,
      enumerable: true,
      configurable: true,
      writable: true
    });
  } else {
    obj[key] = value;
  }

  return obj;
}

function _extends() {
  _extends = Object.assign || function (target) {
    for (var i = 1; i < arguments.length; i++) {
      var source = arguments[i];

      for (var key in source) {
        if (Object.prototype.hasOwnProperty.call(source, key)) {
          target[key] = source[key];
        }
      }
    }

    return target;
  };

  return _extends.apply(this, arguments);
}

function _inherits(subClass, superClass) {
  if (typeof superClass !== "function" && superClass !== null) {
    throw new TypeError("Super expression must either be null or a function");
  }

  subClass.prototype = Object.create(superClass && superClass.prototype, {
    constructor: {
      value: subClass,
      writable: true,
      configurable: true
    }
  });
  if (superClass) _setPrototypeOf(subClass, superClass);
}

function _getPrototypeOf(o) {
  _getPrototypeOf = Object.setPrototypeOf ? Object.getPrototypeOf : function _getPrototypeOf(o) {
    return o.__proto__ || Object.getPrototypeOf(o);
  };
  return _getPrototypeOf(o);
}

function _setPrototypeOf(o, p) {
  _setPrototypeOf = Object.setPrototypeOf || function _setPrototypeOf(o, p) {
    o.__proto__ = p;
    return o;
  };

  return _setPrototypeOf(o, p);
}

function _objectWithoutPropertiesLoose(source, excluded) {
  if (source == null) return {};
  var target = {};
  var sourceKeys = Object.keys(source);
  var key, i;

  for (i = 0; i < sourceKeys.length; i++) {
    key = sourceKeys[i];
    if (excluded.indexOf(key) >= 0) continue;
    target[key] = source[key];
  }

  return target;
}

function _objectWithoutProperties(source, excluded) {
  if (source == null) return {};

  var target = _objectWithoutPropertiesLoose(source, excluded);

  var key, i;

  if (Object.getOwnPropertySymbols) {
    var sourceSymbolKeys = Object.getOwnPropertySymbols(source);

    for (i = 0; i < sourceSymbolKeys.length; i++) {
      key = sourceSymbolKeys[i];
      if (excluded.indexOf(key) >= 0) continue;
      if (!Object.prototype.propertyIsEnumerable.call(source, key)) continue;
      target[key] = source[key];
    }
  }

  return target;
}

function _assertThisInitialized(self) {
  if (self === void 0) {
    throw new ReferenceError("this hasn't been initialised - super() hasn't been called");
  }

  return self;
}

function _possibleConstructorReturn(self, call) {
  if (call && (typeof call === "object" || typeof call === "function")) {
    return call;
  } else if (call !== void 0) {
    throw new TypeError("Derived constructors may only return object or undefined");
  }

  return _assertThisInitialized(self);
}

function _slicedToArray(arr, i) {
  return _arrayWithHoles(arr) || _iterableToArrayLimit(arr, i) || _unsupportedIterableToArray(arr, i) || _nonIterableRest();
}

function _arrayWithHoles(arr) {
  if (Array.isArray(arr)) return arr;
}

function _iterableToArrayLimit(arr, i) {
  var _i = arr == null ? null : typeof Symbol !== "undefined" && arr[Symbol.iterator] || arr["@@iterator"];

  if (_i == null) return;
  var _arr = [];
  var _n = true;
  var _d = false;

  var _s, _e;

  try {
    for (_i = _i.call(arr); !(_n = (_s = _i.next()).done); _n = true) {
      _arr.push(_s.value);

      if (i && _arr.length === i) break;
    }
  } catch (err) {
    _d = true;
    _e = err;
  } finally {
    try {
      if (!_n && _i["return"] != null) _i["return"]();
    } finally {
      if (_d) throw _e;
    }
  }

  return _arr;
}

function _unsupportedIterableToArray(o, minLen) {
  if (!o) return;
  if (typeof o === "string") return _arrayLikeToArray(o, minLen);
  var n = Object.prototype.toString.call(o).slice(8, -1);
  if (n === "Object" && o.constructor) n = o.constructor.name;
  if (n === "Map" || n === "Set") return Array.from(o);
  if (n === "Arguments" || /^(?:Ui|I)nt(?:8|16|32)(?:Clamped)?Array$/.test(n)) return _arrayLikeToArray(o, minLen);
}

function _arrayLikeToArray(arr, len) {
  if (len == null || len > arr.length) len = arr.length;

  for (var i = 0, arr2 = new Array(len); i < len; i++) arr2[i] = arr[i];

  return arr2;
}

function _nonIterableRest() {
  throw new TypeError("Invalid attempt to destructure non-iterable instance.\nIn order to be iterable, non-array objects must have a [Symbol.iterator]() method.");
}

var DeviceTypes = {
  Mobile: 'mobile',
  Tablet: 'tablet',
  SmartTv: 'smarttv',
  Console: 'console',
  Wearable: 'wearable',
  Embedded: 'embedded',
  Browser: undefined
};
var BrowserTypes = {
  Chrome: 'Chrome',
  Firefox: 'Firefox',
  Opera: 'Opera',
  Yandex: 'Yandex',
  Safari: 'Safari',
  InternetExplorer: 'Internet Explorer',
  Edge: 'Edge',
  Chromium: 'Chromium',
  Ie: 'IE',
  MobileSafari: 'Mobile Safari',
  EdgeChromium: 'Edge Chromium',
  MIUI: 'MIUI Browser',
  SamsungBrowser: 'Samsung Browser'
};
var OsTypes = {
  IOS: 'iOS',
  Android: 'Android',
  WindowsPhone: 'Windows Phone',
  Windows: 'Windows',
  MAC_OS: 'Mac OS'
};
var InitialDeviceTypes = {
  isMobile: false,
  isTablet: false,
  isBrowser: false,
  isSmartTV: false,
  isConsole: false,
  isWearable: false
};

var checkDeviceType = function checkDeviceType(type) {
  switch (type) {
    case DeviceTypes.Mobile:
      return {
        isMobile: true
      };

    case DeviceTypes.Tablet:
      return {
        isTablet: true
      };

    case DeviceTypes.SmartTv:
      return {
        isSmartTV: true
      };

    case DeviceTypes.Console:
      return {
        isConsole: true
      };

    case DeviceTypes.Wearable:
      return {
        isWearable: true
      };

    case DeviceTypes.Browser:
      return {
        isBrowser: true
      };

    case DeviceTypes.Embedded:
      return {
        isEmbedded: true
      };

    default:
      return InitialDeviceTypes;
  }
};
var setUserAgent = function setUserAgent(userAgent) {
  return setUa(userAgent);
};
var setDefaults = function setDefaults(p) {
  var d = arguments.length > 1 && arguments[1] !== undefined ? arguments[1] : 'none';
  return p ? p : d;
};
var getNavigatorInstance = function getNavigatorInstance() {
  if (typeof window !== 'undefined') {
    if (window.navigator || navigator) {
      return window.navigator || navigator;
    }
  }

  return false;
};
var isIOS13Check = function isIOS13Check(type) {
  var nav = getNavigatorInstance();
  return nav && nav.platform && (nav.platform.indexOf(type) !== -1 || nav.platform === 'MacIntel' && nav.maxTouchPoints > 1 && !window.MSStream);
};

var browserPayload = function browserPayload(isBrowser, browser, engine, os, ua) {
  return {
    isBrowser: isBrowser,
    browserMajorVersion: setDefaults(browser.major),
    browserFullVersion: setDefaults(browser.version),
    browserName: setDefaults(browser.name),
    engineName: setDefaults(engine.name),
    engineVersion: setDefaults(engine.version),
    osName: setDefaults(os.name),
    osVersion: setDefaults(os.version),
    userAgent: setDefaults(ua)
  };
};
var mobilePayload = function mobilePayload(type, device, os, ua) {
  return _objectSpread2({}, type, {
    vendor: setDefaults(device.vendor),
    model: setDefaults(device.model),
    os: setDefaults(os.name),
    osVersion: setDefaults(os.version),
    ua: setDefaults(ua)
  });
};
var smartTvPayload = function smartTvPayload(isSmartTV, engine, os, ua) {
  return {
    isSmartTV: isSmartTV,
    engineName: setDefaults(engine.name),
    engineVersion: setDefaults(engine.version),
    osName: setDefaults(os.name),
    osVersion: setDefaults(os.version),
    userAgent: setDefaults(ua)
  };
};
var consolePayload = function consolePayload(isConsole, engine, os, ua) {
  return {
    isConsole: isConsole,
    engineName: setDefaults(engine.name),
    engineVersion: setDefaults(engine.version),
    osName: setDefaults(os.name),
    osVersion: setDefaults(os.version),
    userAgent: setDefaults(ua)
  };
};
var wearablePayload = function wearablePayload(isWearable, engine, os, ua) {
  return {
    isWearable: isWearable,
    engineName: setDefaults(engine.name),
    engineVersion: setDefaults(engine.version),
    osName: setDefaults(os.name),
    osVersion: setDefaults(os.version),
    userAgent: setDefaults(ua)
  };
};
var embeddedPayload = function embeddedPayload(isEmbedded, device, engine, os, ua) {
  return {
    isEmbedded: isEmbedded,
    vendor: setDefaults(device.vendor),
    model: setDefaults(device.model),
    engineName: setDefaults(engine.name),
    engineVersion: setDefaults(engine.version),
    osName: setDefaults(os.name),
    osVersion: setDefaults(os.version),
    userAgent: setDefaults(ua)
  };
};

function deviceDetect(userAgent) {
  var _ref = userAgent ? parseUserAgent(userAgent) : UAHelper,
      device = _ref.device,
      browser = _ref.browser,
      engine = _ref.engine,
      os = _ref.os,
      ua = _ref.ua;

  var type = checkDeviceType(device.type);
  var isBrowser = type.isBrowser,
      isMobile = type.isMobile,
      isTablet = type.isTablet,
      isSmartTV = type.isSmartTV,
      isConsole = type.isConsole,
      isWearable = type.isWearable,
      isEmbedded = type.isEmbedded;

  if (isBrowser) {
    return browserPayload(isBrowser, browser, engine, os, ua);
  }

  if (isSmartTV) {
    return smartTvPayload(isSmartTV, engine, os, ua);
  }

  if (isConsole) {
    return consolePayload(isConsole, engine, os, ua);
  }

  if (isMobile) {
    return mobilePayload(type, device, os, ua);
  }

  if (isTablet) {
    return mobilePayload(type, device, os, ua);
  }

  if (isWearable) {
    return wearablePayload(isWearable, engine, os, ua);
  }

  if (isEmbedded) {
    return embeddedPayload(isEmbedded, device, engine, os, ua);
  }
}

var isMobileType = function isMobileType(_ref) {
  var type = _ref.type;
  return type === DeviceTypes.Mobile;
};
var isTabletType = function isTabletType(_ref2) {
  var type = _ref2.type;
  return type === DeviceTypes.Tablet;
};
var isMobileAndTabletType = function isMobileAndTabletType(_ref3) {
  var type = _ref3.type;
  return type === DeviceTypes.Mobile || type === DeviceTypes.Tablet;
};
var isSmartTVType = function isSmartTVType(_ref4) {
  var type = _ref4.type;
  return type === DeviceTypes.SmartTv;
};
var isBrowserType = function isBrowserType(_ref5) {
  var type = _ref5.type;
  return type === DeviceTypes.Browser;
};
var isWearableType = function isWearableType(_ref6) {
  var type = _ref6.type;
  return type === DeviceTypes.Wearable;
};
var isConsoleType = function isConsoleType(_ref7) {
  var type = _ref7.type;
  return type === DeviceTypes.Console;
};
var isEmbeddedType = function isEmbeddedType(_ref8) {
  var type = _ref8.type;
  return type === DeviceTypes.Embedded;
};
var getMobileVendor = function getMobileVendor(_ref9) {
  var vendor = _ref9.vendor;
  return setDefaults(vendor);
};
var getMobileModel = function getMobileModel(_ref10) {
  var model = _ref10.model;
  return setDefaults(model);
};
var getDeviceType = function getDeviceType(_ref11) {
  var type = _ref11.type;
  return setDefaults(type, 'browser');
}; // os types

var isAndroidType = function isAndroidType(_ref12) {
  var name = _ref12.name;
  return name === OsTypes.Android;
};
var isWindowsType = function isWindowsType(_ref13) {
  var name = _ref13.name;
  return name === OsTypes.Windows;
};
var isMacOsType = function isMacOsType(_ref14) {
  var name = _ref14.name;
  return name === OsTypes.MAC_OS;
};
var isWinPhoneType = function isWinPhoneType(_ref15) {
  var name = _ref15.name;
  return name === OsTypes.WindowsPhone;
};
var isIOSType = function isIOSType(_ref16) {
  var name = _ref16.name;
  return name === OsTypes.IOS;
};
var getOsVersion = function getOsVersion(_ref17) {
  var version = _ref17.version;
  return setDefaults(version);
};
var getOsName = function getOsName(_ref18) {
  var name = _ref18.name;
  return setDefaults(name);
}; // browser types

var isChromeType = function isChromeType(_ref19) {
  var name = _ref19.name;
  return name === BrowserTypes.Chrome;
};
var isFirefoxType = function isFirefoxType(_ref20) {
  var name = _ref20.name;
  return name === BrowserTypes.Firefox;
};
var isChromiumType = function isChromiumType(_ref21) {
  var name = _ref21.name;
  return name === BrowserTypes.Chromium;
};
var isEdgeType = function isEdgeType(_ref22) {
  var name = _ref22.name;
  return name === BrowserTypes.Edge;
};
var isYandexType = function isYandexType(_ref23) {
  var name = _ref23.name;
  return name === BrowserTypes.Yandex;
};
var isSafariType = function isSafariType(_ref24) {
  var name = _ref24.name;
  return name === BrowserTypes.Safari || name === BrowserTypes.MobileSafari;
};
var isMobileSafariType = function isMobileSafariType(_ref25) {
  var name = _ref25.name;
  return name === BrowserTypes.MobileSafari;
};
var isOperaType = function isOperaType(_ref26) {
  var name = _ref26.name;
  return name === BrowserTypes.Opera;
};
var isIEType = function isIEType(_ref27) {
  var name = _ref27.name;
  return name === BrowserTypes.InternetExplorer || name === BrowserTypes.Ie;
};
var isMIUIType = function isMIUIType(_ref28) {
  var name = _ref28.name;
  return name === BrowserTypes.MIUI;
};
var isSamsungBrowserType = function isSamsungBrowserType(_ref29) {
  var name = _ref29.name;
  return name === BrowserTypes.SamsungBrowser;
};
var getBrowserFullVersion = function getBrowserFullVersion(_ref30) {
  var version = _ref30.version;
  return setDefaults(version);
};
var getBrowserVersion = function getBrowserVersion(_ref31) {
  var major = _ref31.major;
  return setDefaults(major);
};
var getBrowserName = function getBrowserName(_ref32) {
  var name = _ref32.name;
  return setDefaults(name);
}; // engine types

var getEngineName = function getEngineName(_ref33) {
  var name = _ref33.name;
  return setDefaults(name);
};
var getEngineVersion = function getEngineVersion(_ref34) {
  var version = _ref34.version;
  return setDefaults(version);
};
var isElectronType = function isElectronType() {
  var nav = getNavigatorInstance();
  var ua = nav && nav.userAgent && nav.userAgent.toLowerCase();
  return typeof ua === 'string' ? /electron/.test(ua) : false;
};
var isEdgeChromiumType = function isEdgeChromiumType(ua) {
  return typeof ua === 'string' && ua.indexOf('Edg/') !== -1;
};
var getIOS13 = function getIOS13() {
  var nav = getNavigatorInstance();
  return nav && (/iPad|iPhone|iPod/.test(nav.platform) || nav.platform === 'MacIntel' && nav.maxTouchPoints > 1) && !window.MSStream;
};
var getIPad13 = function getIPad13() {
  return isIOS13Check('iPad');
};
var getIphone13 = function getIphone13() {
  return isIOS13Check('iPhone');
};
var getIPod13 = function getIPod13() {
  return isIOS13Check('iPod');
};
var getUseragent = function getUseragent(userAg) {
  return setDefaults(userAg);
};

function buildSelectorsObject(options) {
  var _ref = options ? options : UAHelper,
      device = _ref.device,
      browser = _ref.browser,
      os = _ref.os,
      engine = _ref.engine,
      ua = _ref.ua;

  return {
    isSmartTV: isSmartTVType(device),
    isConsole: isConsoleType(device),
    isWearable: isWearableType(device),
    isEmbedded: isEmbeddedType(device),
    isMobileSafari: isMobileSafariType(browser) || getIPad13(),
    isChromium: isChromiumType(browser),
    isMobile: isMobileAndTabletType(device) || getIPad13(),
    isMobileOnly: isMobileType(device),
    isTablet: isTabletType(device) || getIPad13(),
    isBrowser: isBrowserType(device),
    isDesktop: isBrowserType(device),
    isAndroid: isAndroidType(os),
    isWinPhone: isWinPhoneType(os),
    isIOS: isIOSType(os) || getIPad13(),
    isChrome: isChromeType(browser),
    isFirefox: isFirefoxType(browser),
    isSafari: isSafariType(browser),
    isOpera: isOperaType(browser),
    isIE: isIEType(browser),
    osVersion: getOsVersion(os),
    osName: getOsName(os),
    fullBrowserVersion: getBrowserFullVersion(browser),
    browserVersion: getBrowserVersion(browser),
    browserName: getBrowserName(browser),
    mobileVendor: getMobileVendor(device),
    mobileModel: getMobileModel(device),
    engineName: getEngineName(engine),
    engineVersion: getEngineVersion(engine),
    getUA: getUseragent(ua),
    isEdge: isEdgeType(browser) || isEdgeChromiumType(ua),
    isYandex: isYandexType(browser),
    deviceType: getDeviceType(device),
    isIOS13: getIOS13(),
    isIPad13: getIPad13(),
    isIPhone13: getIphone13(),
    isIPod13: getIPod13(),
    isElectron: isElectronType(),
    isEdgeChromium: isEdgeChromiumType(ua),
    isLegacyEdge: isEdgeType(browser) && !isEdgeChromiumType(ua),
    isWindows: isWindowsType(os),
    isMacOs: isMacOsType(os),
    isMIUI: isMIUIType(browser),
    isSamsungBrowser: isSamsungBrowserType(browser)
  };
}

var isSmartTV = isSmartTVType(device);
var isConsole = isConsoleType(device);
var isWearable = isWearableType(device);
var isEmbedded = isEmbeddedType(device);
var isMobileSafari = isMobileSafariType(browser) || getIPad13();
var isChromium = isChromiumType(browser);
var isMobile = isMobileAndTabletType(device) || getIPad13();
var isMobileOnly = isMobileType(device);
var isTablet = isTabletType(device) || getIPad13();
var isBrowser = isBrowserType(device);
var isDesktop = isBrowserType(device);
var isAndroid = isAndroidType(os);
var isWinPhone = isWinPhoneType(os);
var isIOS = isIOSType(os) || getIPad13();
var isChrome = isChromeType(browser);
var isFirefox = isFirefoxType(browser);
var isSafari = isSafariType(browser);
var isOpera = isOperaType(browser);
var isIE = isIEType(browser);
var osVersion = getOsVersion(os);
var osName = getOsName(os);
var fullBrowserVersion = getBrowserFullVersion(browser);
var browserVersion = getBrowserVersion(browser);
var browserName = getBrowserName(browser);
var mobileVendor = getMobileVendor(device);
var mobileModel = getMobileModel(device);
var engineName = getEngineName(engine);
var engineVersion = getEngineVersion(engine);
var getUA = getUseragent(ua);
var isEdge = isEdgeType(browser) || isEdgeChromiumType(ua);
var isYandex = isYandexType(browser);
var deviceType = getDeviceType(device);
var isIOS13 = getIOS13();
var isIPad13 = getIPad13();
var isIPhone13 = getIphone13();
var isIPod13 = getIPod13();
var isElectron = isElectronType();
var isEdgeChromium = isEdgeChromiumType(ua);
var isLegacyEdge = isEdgeType(browser) && !isEdgeChromiumType(ua);
var isWindows = isWindowsType(os);
var isMacOs = isMacOsType(os);
var isMIUI = isMIUIType(browser);
var isSamsungBrowser = isSamsungBrowserType(browser);
var getSelectorsByUserAgent = function getSelectorsByUserAgent(userAgent) {
  if (!userAgent || typeof userAgent !== 'string') {
    console.error('No valid user agent string was provided');
    return;
  }

  var _UAHelper$parseUserAg = parseUserAgent(userAgent),
      device = _UAHelper$parseUserAg.device,
      browser = _UAHelper$parseUserAg.browser,
      os = _UAHelper$parseUserAg.os,
      engine = _UAHelper$parseUserAg.engine,
      ua = _UAHelper$parseUserAg.ua;

  return buildSelectorsObject({
    device: device,
    browser: browser,
    os: os,
    engine: engine,
    ua: ua
  });
};

var AndroidView = function AndroidView(_ref) {
  var renderWithFragment = _ref.renderWithFragment,
      children = _ref.children,
      props = _objectWithoutProperties(_ref, ["renderWithFragment", "children"]);

  return isAndroid ? renderWithFragment ? React__default.createElement(React.Fragment, null, children) : React__default.createElement("div", props, children) : null;
};
var BrowserView = function BrowserView(_ref2) {
  var renderWithFragment = _ref2.renderWithFragment,
      children = _ref2.children,
      props = _objectWithoutProperties(_ref2, ["renderWithFragment", "children"]);

  return isBrowser ? renderWithFragment ? React__default.createElement(React.Fragment, null, children) : React__default.createElement("div", props, children) : null;
};
var IEView = function IEView(_ref3) {
  var renderWithFragment = _ref3.renderWithFragment,
      children = _ref3.children,
      props = _objectWithoutProperties(_ref3, ["renderWithFragment", "children"]);

  return isIE ? renderWithFragment ? React__default.createElement(React.Fragment, null, children) : React__default.createElement("div", props, children) : null;
};
var IOSView = function IOSView(_ref4) {
  var renderWithFragment = _ref4.renderWithFragment,
      children = _ref4.children,
      props = _objectWithoutProperties(_ref4, ["renderWithFragment", "children"]);

  return isIOS ? renderWithFragment ? React__default.createElement(React.Fragment, null, children) : React__default.createElement("div", props, children) : null;
};
var MobileView = function MobileView(_ref5) {
  var renderWithFragment = _ref5.renderWithFragment,
      children = _ref5.children,
      props = _objectWithoutProperties(_ref5, ["renderWithFragment", "children"]);

  return isMobile ? renderWithFragment ? React__default.createElement(React.Fragment, null, children) : React__default.createElement("div", props, children) : null;
};
var TabletView = function TabletView(_ref6) {
  var renderWithFragment = _ref6.renderWithFragment,
      children = _ref6.children,
      props = _objectWithoutProperties(_ref6, ["renderWithFragment", "children"]);

  return isTablet ? renderWithFragment ? React__default.createElement(React.Fragment, null, children) : React__default.createElement("div", props, children) : null;
};
var WinPhoneView = function WinPhoneView(_ref7) {
  var renderWithFragment = _ref7.renderWithFragment,
      children = _ref7.children,
      props = _objectWithoutProperties(_ref7, ["renderWithFragment", "children"]);

  return isWinPhone ? renderWithFragment ? React__default.createElement(React.Fragment, null, children) : React__default.createElement("div", props, children) : null;
};
var MobileOnlyView = function MobileOnlyView(_ref8) {
  var renderWithFragment = _ref8.renderWithFragment,
      children = _ref8.children;
      _ref8.viewClassName;
      _ref8.style;
      var props = _objectWithoutProperties(_ref8, ["renderWithFragment", "children", "viewClassName", "style"]);

  return isMobileOnly ? renderWithFragment ? React__default.createElement(React.Fragment, null, children) : React__default.createElement("div", props, children) : null;
};
var SmartTVView = function SmartTVView(_ref9) {
  var renderWithFragment = _ref9.renderWithFragment,
      children = _ref9.children,
      props = _objectWithoutProperties(_ref9, ["renderWithFragment", "children"]);

  return isSmartTV ? renderWithFragment ? React__default.createElement(React.Fragment, null, children) : React__default.createElement("div", props, children) : null;
};
var ConsoleView = function ConsoleView(_ref10) {
  var renderWithFragment = _ref10.renderWithFragment,
      children = _ref10.children,
      props = _objectWithoutProperties(_ref10, ["renderWithFragment", "children"]);

  return isConsole ? renderWithFragment ? React__default.createElement(React.Fragment, null, children) : React__default.createElement("div", props, children) : null;
};
var WearableView = function WearableView(_ref11) {
  var renderWithFragment = _ref11.renderWithFragment,
      children = _ref11.children,
      props = _objectWithoutProperties(_ref11, ["renderWithFragment", "children"]);

  return isWearable ? renderWithFragment ? React__default.createElement(React.Fragment, null, children) : React__default.createElement("div", props, children) : null;
};
var CustomView = function CustomView(_ref12) {
  var renderWithFragment = _ref12.renderWithFragment,
      children = _ref12.children;
      _ref12.viewClassName;
      _ref12.style;
      var condition = _ref12.condition,
      props = _objectWithoutProperties(_ref12, ["renderWithFragment", "children", "viewClassName", "style", "condition"]);

  return condition ? renderWithFragment ? React__default.createElement(React.Fragment, null, children) : React__default.createElement("div", props, children) : null;
};

function withOrientationChange(WrappedComponent) {
  return /*#__PURE__*/function (_React$Component) {
    _inherits(_class, _React$Component);

    function _class(props) {
      var _this;

      _classCallCheck(this, _class);

      _this = _possibleConstructorReturn(this, _getPrototypeOf(_class).call(this, props));
      _this.isEventListenerAdded = false;
      _this.handleOrientationChange = _this.handleOrientationChange.bind(_assertThisInitialized(_this));
      _this.onOrientationChange = _this.onOrientationChange.bind(_assertThisInitialized(_this));
      _this.onPageLoad = _this.onPageLoad.bind(_assertThisInitialized(_this));
      _this.state = {
        isLandscape: false,
        isPortrait: false
      };
      return _this;
    }

    _createClass(_class, [{
      key: "handleOrientationChange",
      value: function handleOrientationChange() {
        if (!this.isEventListenerAdded) {
          this.isEventListenerAdded = true;
        }

        var orientation = window.innerWidth > window.innerHeight ? 90 : 0;
        this.setState({
          isPortrait: orientation === 0,
          isLandscape: orientation === 90
        });
      }
    }, {
      key: "onOrientationChange",
      value: function onOrientationChange() {
        this.handleOrientationChange();
      }
    }, {
      key: "onPageLoad",
      value: function onPageLoad() {
        this.handleOrientationChange();
      }
    }, {
      key: "componentDidMount",
      value: function componentDidMount() {
        if ((typeof window === "undefined" ? "undefined" : _typeof(window)) !== undefined && isMobile) {
          if (!this.isEventListenerAdded) {
            this.handleOrientationChange();
            window.addEventListener("load", this.onPageLoad, false);
          } else {
            window.removeEventListener("load", this.onPageLoad, false);
          }

          window.addEventListener("resize", this.onOrientationChange, false);
        }
      }
    }, {
      key: "componentWillUnmount",
      value: function componentWillUnmount() {
        window.removeEventListener("resize", this.onOrientationChange, false);
      }
    }, {
      key: "render",
      value: function render() {
        return React__default.createElement(WrappedComponent, _extends({}, this.props, {
          isLandscape: this.state.isLandscape,
          isPortrait: this.state.isPortrait
        }));
      }
    }]);

    return _class;
  }(React__default.Component);
}

function useMobileOrientation() {
  var _useState = React.useState(function () {
    var orientation = window.innerWidth > window.innerHeight ? 90 : 0;
    return {
      isPortrait: orientation === 0,
      isLandscape: orientation === 90,
      orientation: orientation === 0 ? 'portrait' : 'landscape'
    };
  }),
      _useState2 = _slicedToArray(_useState, 2),
      state = _useState2[0],
      setState = _useState2[1];

  var handleOrientationChange = React.useCallback(function () {
    var orientation = window.innerWidth > window.innerHeight ? 90 : 0;
    var next = {
      isPortrait: orientation === 0,
      isLandscape: orientation === 90,
      orientation: orientation === 0 ? 'portrait' : 'landscape'
    };
    state.orientation !== next.orientation && setState(next);
  }, [state.orientation]);
  React.useEffect(function () {
    if ((typeof window === "undefined" ? "undefined" : _typeof(window)) !== undefined && isMobile) {
      handleOrientationChange();
      window.addEventListener("load", handleOrientationChange, false);
      window.addEventListener("resize", handleOrientationChange, false);
    }

    return function () {
      window.removeEventListener("resize", handleOrientationChange, false);
      window.removeEventListener("load", handleOrientationChange, false);
    };
  }, [handleOrientationChange]);
  return state;
}

function useDeviceData(userAgent) {
  var hookUserAgent = userAgent ? userAgent : window.navigator.userAgent;
  return parseUserAgent(hookUserAgent);
}

function useDeviceSelectors(userAgent) {
  var hookUserAgent = userAgent ? userAgent : window.navigator.userAgent;
  var deviceData = useDeviceData(hookUserAgent);
  var selectors = buildSelectorsObject(deviceData);
  return [selectors, deviceData];
}

lib.AndroidView = AndroidView;
lib.BrowserTypes = BrowserTypes;
lib.BrowserView = BrowserView;
lib.ConsoleView = ConsoleView;
lib.CustomView = CustomView;
lib.IEView = IEView;
lib.IOSView = IOSView;
lib.MobileOnlyView = MobileOnlyView;
lib.MobileView = MobileView;
lib.OsTypes = OsTypes;
lib.SmartTVView = SmartTVView;
lib.TabletView = TabletView;
lib.WearableView = WearableView;
lib.WinPhoneView = WinPhoneView;
lib.browserName = browserName;
lib.browserVersion = browserVersion;
lib.deviceDetect = deviceDetect;
lib.deviceType = deviceType;
lib.engineName = engineName;
lib.engineVersion = engineVersion;
lib.fullBrowserVersion = fullBrowserVersion;
lib.getSelectorsByUserAgent = getSelectorsByUserAgent;
lib.getUA = getUA;
lib.isAndroid = isAndroid;
lib.isBrowser = isBrowser;
lib.isChrome = isChrome;
lib.isChromium = isChromium;
lib.isConsole = isConsole;
lib.isDesktop = isDesktop;
lib.isEdge = isEdge;
lib.isEdgeChromium = isEdgeChromium;
lib.isElectron = isElectron;
lib.isEmbedded = isEmbedded;
lib.isFirefox = isFirefox;
lib.isIE = isIE;
lib.isIOS = isIOS;
lib.isIOS13 = isIOS13;
lib.isIPad13 = isIPad13;
lib.isIPhone13 = isIPhone13;
lib.isIPod13 = isIPod13;
lib.isLegacyEdge = isLegacyEdge;
lib.isMIUI = isMIUI;
lib.isMacOs = isMacOs;
var isMobile_1 = lib.isMobile = isMobile;
lib.isMobileOnly = isMobileOnly;
lib.isMobileSafari = isMobileSafari;
lib.isOpera = isOpera;
lib.isSafari = isSafari;
lib.isSamsungBrowser = isSamsungBrowser;
lib.isSmartTV = isSmartTV;
lib.isTablet = isTablet;
lib.isWearable = isWearable;
lib.isWinPhone = isWinPhone;
lib.isWindows = isWindows;
lib.isYandex = isYandex;
lib.mobileModel = mobileModel;
lib.mobileVendor = mobileVendor;
lib.osName = osName;
lib.osVersion = osVersion;
lib.parseUserAgent = parseUserAgent;
lib.setUserAgent = setUserAgent;
lib.useDeviceData = useDeviceData;
lib.useDeviceSelectors = useDeviceSelectors;
lib.useMobileOrientation = useMobileOrientation;
lib.withOrientationChange = withOrientationChange;

var createGroupsInArray = function (arr, numberOfGroups) {
    var perGroup = Math.ceil(arr.length / numberOfGroups);
    return Array.from({ length: numberOfGroups })
        .fill('')
        .map(function (_, i) { return arr.slice(i * perGroup, (i + 1) * perGroup); });
};
var getMonthsNames = function (locale) {
    var months = [];
    var d = new Date();
    d.setDate(1);
    for (var i = 0; i < 12; i++) {
        d.setMonth(i);
        months.push(d.toLocaleString(locale, { month: 'short' }));
    }
    return months;
};
var getYears = function (year) {
    var years = [];
    for (var _year = year - 6; _year < year + 6; _year++) {
        years.push(_year);
    }
    return years;
};
var getLeadingDays = function (year, month, firstDayOfWeek) {
    // 0: sunday
    // 1: monday
    var dates = [];
    var d = new Date(year, month);
    var y = d.getFullYear();
    var m = d.getMonth();
    var firstWeekday = new Date(y, m, 1).getDay();
    var leadingDays = 6 - (6 - firstWeekday) - firstDayOfWeek;
    if (firstDayOfWeek) {
        leadingDays = leadingDays < 0 ? 7 + leadingDays : leadingDays;
    }
    for (var i = leadingDays * -1; i < 0; i++) {
        dates.push({
            date: new Date(y, m, i + 1),
            month: 'previous',
        });
    }
    return dates;
};
var getMonthDays = function (year, month) {
    var dates = [];
    var lastDay = new Date(year, month + 1, 0).getDate();
    for (var i = 1; i <= lastDay; i++) {
        dates.push({
            date: new Date(year, month, i),
            month: 'current',
        });
    }
    return dates;
};
var getTrailingDays = function (year, month, leadingDays, monthDays) {
    var dates = [];
    var days = 42 - (leadingDays.length + monthDays.length);
    for (var i = 1; i <= days; i++) {
        dates.push({
            date: new Date(year, month + 1, i),
            month: 'next',
        });
    }
    return dates;
};
var getMonthDetails = function (year, month, firstDayOfWeek) {
    var daysPrevMonth = getLeadingDays(year, month, firstDayOfWeek);
    var daysThisMonth = getMonthDays(year, month);
    var daysNextMonth = getTrailingDays(year, month, daysPrevMonth, daysThisMonth);
    var days = __spreadArray(__spreadArray(__spreadArray([], daysPrevMonth, true), daysThisMonth, true), daysNextMonth, true);
    var weeks = [];
    days.forEach(function (day, index) {
        if (index % 7 === 0 || weeks.length === 0) {
            weeks.push([]);
        }
        weeks[weeks.length - 1].push(day);
    });
    return weeks;
};
var isDisableDateInRange = function (startDate, endDate, dates) {
    if (startDate && endDate) {
        var date = new Date(startDate);
        var disabled = false;
        while (date < endDate) {
            date.setDate(date.getDate() + 1);
            if (isDateDisabled(date, null, null, dates)) {
                disabled = true;
                break;
            }
        }
        return disabled;
    }
    return false;
};
var isDateDisabled = function (date, min, max, dates) {
    var disabled;
    if (dates) {
        dates.forEach(function (_date) {
            if (Array.isArray(_date) && isDateInRange(date, _date[0], _date[1])) {
                disabled = true;
            }
            if (_date instanceof Date && isSameDateAs(date, _date)) {
                disabled = true;
            }
        });
    }
    if (min && date < min) {
        disabled = true;
    }
    if (max && date > max) {
        disabled = true;
    }
    return disabled;
};
var isDateInRange = function (date, start, end) {
    return start && end && start <= date && date <= end;
};
var isDateSelected = function (date, start, end) {
    return (start && isSameDateAs(start, date)) || (end && isSameDateAs(end, date));
};
var isEndDate = function (date, start, end) {
    return start && end && isSameDateAs(end, date) && start < end;
};
var isLastDayOfMonth = function (date) {
    var test = new Date(date.getTime());
    var month = test.getMonth();
    test.setDate(test.getDate() + 1);
    return test.getMonth() !== month;
};
var isSameDateAs = function (date, date2) {
    if (date instanceof Date && date2 instanceof Date) {
        return (date.getDate() === date2.getDate() &&
            date.getMonth() === date2.getMonth() &&
            date.getFullYear() === date2.getFullYear());
    }
    if (date === null && date2 === null) {
        return true;
    }
    return false;
};
var isStartDate = function (date, start, end) {
    return start && end && isSameDateAs(start, date) && start < end;
};
var isToday = function (date) {
    var today = new Date();
    return (date.getDate() === today.getDate() &&
        date.getMonth() === today.getMonth() &&
        date.getFullYear() === today.getFullYear());
};

var Calendar = function (props) {
    var addMonths = props.addMonths, calendarDate = props.calendarDate, dayFormat = props.dayFormat, disabledDates = props.disabledDates, endDate = props.endDate, firstDayOfWeek = props.firstDayOfWeek, hoverDate = props.hoverDate, locale = props.locale, maxDate = props.maxDate, minDate = props.minDate, onDayClick = props.onDayClick, onDayKeyDown = props.onDayKeyDown, onDayMouseEnter = props.onDayMouseEnter, onDayMouseLeave = props.onDayMouseLeave, onMonthClick = props.onMonthClick, onMonthKeyDown = props.onMonthKeyDown, onYearClick = props.onYearClick, onYearKeyDown = props.onYearKeyDown, selectAdjacementDays = props.selectAdjacementDays, selectEndDate = props.selectEndDate, showAdjacementDays = props.showAdjacementDays, startDate = props.startDate, view = props.view, weekdayFormat = props.weekdayFormat;
    var _a = React$1.useState(calendarDate), date = _a[0], setDate = _a[1];
    var _b = React$1.useState([]), listOfMonths = _b[0], setListOfMonths = _b[1];
    React$1.useEffect(function () {
        if (addMonths !== 0) {
            setDate(new Date(calendarDate.getFullYear(), calendarDate.getMonth() + addMonths, 1));
            return;
        }
        setDate(calendarDate);
    }, [calendarDate]);
    React$1.useEffect(function () {
        setListOfMonths(createGroupsInArray(getMonthsNames(locale), 4));
    }, []);
    var monthDetails = getMonthDetails(date.getFullYear(), date.getMonth(), firstDayOfWeek);
    var listOfYears = createGroupsInArray(getYears(date.getFullYear()), 4);
    var weekDays = monthDetails[0];
    return (React$1.createElement("table", null,
        view === 'days' && (React$1.createElement("thead", null,
            React$1.createElement("tr", null, weekDays.map(function (_a, idx) {
                var date = _a.date;
                return (React$1.createElement("th", { key: idx, className: "calendar-cell" },
                    React$1.createElement("div", { className: "calendar-header-cell-inner" }, typeof weekdayFormat === 'function'
                        ? weekdayFormat(date)
                        : (typeof weekdayFormat === 'string'
                            ? date.toLocaleDateString(locale, { weekday: weekdayFormat })
                            : date.toLocaleDateString(locale, { weekday: 'long' }).slice(0, weekdayFormat)))));
            })))),
        React$1.createElement("tbody", null,
            view === 'days' &&
                monthDetails.map(function (week, index) {
                    return (React$1.createElement("tr", { key: index }, week.map(function (_a, idx) {
                        var _b;
                        var date = _a.date, month = _a.month;
                        return month === 'current' || showAdjacementDays ? (React$1.createElement("td", __assign$1({ className: classNames$1('calendar-cell', (_b = {
                                    today: month === 'current' && isToday(date),
                                    disabled: isDateDisabled(date, minDate, maxDate, disabledDates)
                                },
                                _b[month] = true,
                                _b.clickable = month !== 'current' && selectAdjacementDays,
                                _b.last = isLastDayOfMonth(date),
                                _b['range-hover'] = month === 'current' &&
                                    (hoverDate && selectEndDate
                                        ? isDateInRange(date, startDate, hoverDate)
                                        : isDateInRange(date, hoverDate, endDate)),
                                _b.range = month === 'current' && isDateInRange(date, startDate, endDate),
                                _b.selected = isDateSelected(date, startDate, endDate),
                                _b.start = isStartDate(date, startDate, endDate),
                                _b.end = isEndDate(date, startDate, endDate),
                                _b)), key: idx, tabIndex: (month === 'current' || selectAdjacementDays) &&
                                !isDateDisabled(date, minDate, maxDate, disabledDates)
                                ? 0
                                : -1, title: date.toLocaleDateString(locale) }, ((month === 'current' || selectAdjacementDays) && {
                            onBlur: function () { return onDayMouseLeave(); },
                            onClick: function () { return onDayClick(date); },
                            onFocus: function () { return onDayMouseEnter(date); },
                            onKeyDown: function (event) { return onDayKeyDown(event, date); },
                            onMouseEnter: function () { return onDayMouseEnter(date); },
                            onMouseLeave: function () { return onDayMouseLeave(); },
                        }), (month !== 'current' &&
                            !selectAdjacementDays && {
                            onMouseEnter: function () { return onDayMouseLeave(); },
                        })),
                            React$1.createElement("div", { className: "calendar-cell-inner" }, typeof dayFormat === 'function'
                                ? dayFormat(date)
                                : date.toLocaleDateString(locale, { day: dayFormat })))) : (React$1.createElement("td", { key: idx }));
                    })));
                }),
            view === 'months' &&
                listOfMonths.map(function (row, index) {
                    return (React$1.createElement("tr", { key: index }, row.map(function (month, idx) {
                        return (React$1.createElement("td", { className: "calendar-cell month", key: idx, onClick: function () { return onMonthClick(index * 3 + idx - addMonths); }, onKeyDown: function (event) { return onMonthKeyDown(event, index * 3 + idx - addMonths); }, tabIndex: 0 },
                            React$1.createElement("div", { className: "calendar-cell-inner" }, month)));
                    })));
                }),
            view === 'years' &&
                listOfYears.map(function (row, index) {
                    return (React$1.createElement("tr", { key: index }, row.map(function (year, idx) {
                        return (React$1.createElement("td", { className: "calendar-cell year", key: idx, onClick: function () {
                                return onYearClick(new Date(year, date.getMonth() - addMonths, date.getDate()));
                            }, onKeyDown: function (event) {
                                return onYearKeyDown(event, new Date(year, date.getMonth() - addMonths, date.getDate()));
                            }, tabIndex: 0 },
                            React$1.createElement("div", { className: "calendar-cell-inner" }, new Date(year, 0, 1).toLocaleDateString(locale, { year: 'numeric' }))));
                    })));
                }))));
};
var Navigation = function (props) {
    var addMonths = props.addMonths, calendarDate = props.calendarDate, locale = props.locale, navigation = props.navigation, navNextDoubleIcon = props.navNextDoubleIcon, navNextIcon = props.navNextIcon, navPrevDoubleIcon = props.navPrevDoubleIcon, navPrevIcon = props.navPrevIcon, navYearFirst = props.navYearFirst, onMonthClick = props.onMonthClick, onNavigationClick = props.onNavigationClick, onYearClick = props.onYearClick, view = props.view;
    var _a = React$1.useState(), date = _a[0], setDate = _a[1];
    React$1.useEffect(function () {
        if (addMonths !== 0) {
            setDate(new Date(calendarDate.getFullYear(), calendarDate.getMonth() + addMonths, 1));
            return;
        }
        setDate(calendarDate);
    }, [calendarDate]);
    return (React$1.createElement("div", { className: "calendar-nav" },
        navigation && (React$1.createElement("div", { className: "calendar-nav-prev" },
            React$1.createElement(CButton, { color: "transparent", size: "sm", onClick: function () { return onNavigationClick('prev', true); } }, navPrevDoubleIcon !== null && navPrevDoubleIcon !== void 0 ? navPrevDoubleIcon : (React$1.createElement("span", { className: "calendar-nav-icon calendar-nav-icon-double-prev" }))),
            view === 'days' && (React$1.createElement(CButton, { color: "transparent", size: "sm", onClick: function () { return onNavigationClick('prev'); } }, navPrevIcon !== null && navPrevIcon !== void 0 ? navPrevIcon : React$1.createElement("span", { className: "calendar-nav-icon calendar-nav-icon-prev" }))))),
        React$1.createElement("div", __assign$1({ className: "calendar-nav-date" }, (navYearFirst && { style: { display: 'flex', justifyContent: 'center' } })),
            view === 'days' && (React$1.createElement(CButton, { color: "transparent", size: "sm", onClick: function () { return navigation && onMonthClick(); } }, date && date.toLocaleDateString(locale, { month: 'long' }))),
            React$1.createElement(CButton, __assign$1({ color: "transparent", size: "sm", onClick: function () { return navigation && onYearClick(); } }, (navYearFirst && { style: { order: '-1' } })), date && date.toLocaleDateString(locale, { year: 'numeric' }))),
        navigation && (React$1.createElement("div", { className: "calendar-nav-next" },
            view === 'days' && (React$1.createElement(CButton, { color: "transparent", size: "sm", onClick: function () { return onNavigationClick('next'); } }, navNextIcon !== null && navNextIcon !== void 0 ? navNextIcon : React$1.createElement("span", { className: "calendar-nav-icon calendar-nav-icon-next" }))),
            React$1.createElement(CButton, { color: "transparent", size: "sm", onClick: function () { return onNavigationClick('next', true); } }, navNextDoubleIcon !== null && navNextDoubleIcon !== void 0 ? navNextDoubleIcon : (React$1.createElement("span", { className: "calendar-nav-icon calendar-nav-icon-double-next" })))))));
};
var CCalendar = React$1.forwardRef(function (_a, ref) {
    var startDate = _a.startDate, endDate = _a.endDate, _b = _a.calendarDate, calendarDate = _b === void 0 ? startDate || endDate || null : _b, _c = _a.calendars, calendars = _c === void 0 ? 1 : _c, className = _a.className, _d = _a.dayFormat, dayFormat = _d === void 0 ? 'numeric' : _d, disabledDates = _a.disabledDates, _e = _a.firstDayOfWeek, firstDayOfWeek = _e === void 0 ? 1 : _e, _f = _a.locale, locale = _f === void 0 ? 'default' : _f, maxDate = _a.maxDate, minDate = _a.minDate, _g = _a.navigation, navigation = _g === void 0 ? true : _g, navNextIcon = _a.navNextIcon, navNextDoubleIcon = _a.navNextDoubleIcon, navPrevIcon = _a.navPrevIcon, navPrevDoubleIcon = _a.navPrevDoubleIcon, navYearFirst = _a.navYearFirst, range = _a.range, _h = _a.selectAdjacementDays, selectAdjacementDays = _h === void 0 ? false : _h, selectEndDate = _a.selectEndDate, _j = _a.showAdjacementDays, showAdjacementDays = _j === void 0 ? true : _j, _k = _a.weekdayFormat, weekdayFormat = _k === void 0 ? 2 : _k, onDayHover = _a.onDayHover, onCalendarDateChange = _a.onCalendarDateChange, onEndDateChange = _a.onEndDateChange, onStartDateChange = _a.onStartDateChange, onSelectEndChange = _a.onSelectEndChange, onViewChanged = _a.onViewChanged;
    var isInitialMount = React$1.useRef(true);
    var _l = React$1.useState(null), _calendarDate = _l[0], setCalendarDate = _l[1];
    React$1.useEffect(function () {
        if (calendarDate === null) {
            setCalendarDate(new Date());
            return;
        }
        if (calendarDate) {
            var date = new Date(calendarDate);
            !isSameDateAs(_calendarDate, date) && setCalendarDate(date);
        }
    }, [calendarDate]);
    var _m = useStateWithCallback(startDate ? new Date(startDate) : null, onStartDateChange, !isInitialMount.current), _startDate = _m[0], setStartDate = _m[1];
    React$1.useEffect(function () {
        var date = startDate ? new Date(startDate) : null;
        if (!isSameDateAs(date, _startDate)) {
            setStartDate(date);
        }
    }, [startDate]);
    var _o = useStateWithCallback(endDate ? new Date(endDate) : null, onEndDateChange, !isInitialMount.current), _endDate = _o[0], setEndDate = _o[1];
    React$1.useEffect(function () {
        var date = endDate ? new Date(endDate) : null;
        if (!isSameDateAs(date, _endDate)) {
            setEndDate(date);
        }
    }, [endDate]);
    var _p = React$1.useState(null), _hoverDate = _p[0], setHoverDate = _p[1];
    var _q = React$1.useState(maxDate ? new Date(maxDate) : null), _maxDate = _q[0], setMaxDate = _q[1];
    React$1.useEffect(function () {
        maxDate && setMaxDate(new Date(maxDate));
    }, [maxDate]);
    var _r = React$1.useState(minDate ? new Date(minDate) : null), _minDate = _r[0], setMinDate = _r[1];
    React$1.useEffect(function () {
        minDate && setMinDate(new Date(minDate));
    }, [minDate]);
    var _s = useStateWithCallback(selectEndDate, onSelectEndChange), _selectEndDate = _s[0], setSelectEndDate = _s[1];
    React$1.useEffect(function () {
        setSelectEndDate(selectEndDate);
    }, [selectEndDate]);
    React$1.useEffect(function () {
        !isInitialMount.current &&
            typeof _selectEndDate === 'boolean' &&
            onSelectEndChange &&
            onSelectEndChange(_selectEndDate);
    }, [_selectEndDate]);
    var _t = useStateWithCallback('days', onViewChanged), view = _t[0], setView = _t[1];
    React$1.useEffect(function () {
        isInitialMount.current = false;
    }, []);
    var setCalendarPage = function (years, months, setMonth) {
        if (months === void 0) { months = 0; }
        if (_calendarDate === null) {
            return;
        }
        var year = _calendarDate.getFullYear();
        var month = _calendarDate.getMonth();
        var d = new Date(year, month, 1);
        years && d.setFullYear(d.getFullYear() + years);
        months && d.setMonth(d.getMonth() + months);
        typeof setMonth === 'number' && d.setMonth(setMonth);
        setCalendarDate(d);
        onCalendarDateChange && onCalendarDateChange(d);
    };
    var handleDayClick = function (date, index) {
        if (isDateDisabled(date, _minDate, _maxDate, disabledDates)) {
            return;
        }
        var _date = new Date(date);
        setCalendarDate(index ? new Date(_date.setMonth(_date.getMonth() - index)) : _date);
        if (range) {
            if (_selectEndDate) {
                setSelectEndDate(false);
                if (_startDate && _startDate > date) {
                    setStartDate(null);
                    setEndDate(null);
                    return;
                }
                if (isDisableDateInRange(_startDate, date, disabledDates)) {
                    setStartDate(null);
                    setEndDate(null);
                    return;
                }
                setEndDate(date);
                return;
            }
            if (_endDate && _endDate < date) {
                setStartDate(null);
                setEndDate(null);
                return;
            }
            if (isDisableDateInRange(date, _endDate, disabledDates)) {
                setStartDate(null);
                setEndDate(null);
                return;
            }
            setSelectEndDate(true);
            setStartDate(date);
            return;
        }
        setStartDate(date);
    };
    var handleDayKeyDown = function (event, date, index) {
        if (event.code === 'Space' || event.key === 'Enter') {
            event.preventDefault();
            handleDayClick(date, index);
        }
    };
    var handleDayMouseEnter = function (date) {
        if (isDateDisabled(date, _minDate, _maxDate, disabledDates)) {
            return;
        }
        setHoverDate(date);
        onDayHover && onDayHover(date);
    };
    var handleDayMouseLeave = function () {
        setHoverDate(null);
        onDayHover && onDayHover(null);
    };
    var handleMonthClick = function (month) {
        setCalendarPage(0, 0, month);
        setView('days');
    };
    var handleMonthKeyDown = function (event, month) {
        if (event.code === 'Space' || event.key === 'Enter') {
            handleMonthClick(month);
        }
    };
    var handleNavigationOnClick = function (direction, double) {
        if (double === void 0) { double = false; }
        if (direction === 'prev') {
            if (double) {
                setCalendarPage(view === 'years' ? -10 : -1);
                return;
            }
            if (view !== 'days') {
                setCalendarPage(-1);
                return;
            }
            setCalendarPage(0, -1);
            return;
        }
        if (direction === 'next') {
            if (double) {
                setCalendarPage(view === 'years' ? 10 : 1);
                return;
            }
            if (view !== 'days') {
                setCalendarPage(1);
                return;
            }
            setCalendarPage(0, 1);
            return;
        }
    };
    var handleYearClick = function (date) {
        setCalendarDate(date);
        setView('months');
    };
    var handleYearKeyDown = function (event, date) {
        if (event.code === 'Space' || event.key === 'Enter') {
            handleYearClick(date);
        }
    };
    return (React$1.createElement("div", { className: classNames$1('calendars', className) }, _calendarDate &&
        Array.from({ length: calendars }, function (_, index) { return (React$1.createElement("div", { className: classNames$1('calendar', view), key: index, ref: ref },
            React$1.createElement(Navigation, { addMonths: index, calendarDate: _calendarDate, locale: locale, navigation: navigation, navNextDoubleIcon: navNextDoubleIcon, navNextIcon: navNextIcon, navPrevDoubleIcon: navPrevDoubleIcon, navPrevIcon: navPrevIcon, navYearFirst: navYearFirst, onMonthClick: function () { return setView('months'); }, onNavigationClick: handleNavigationOnClick, onYearClick: function () { return setView('years'); }, view: view }),
            React$1.createElement(Calendar, { addMonths: index, calendarDate: _calendarDate, dayFormat: dayFormat, disabledDates: disabledDates, endDate: _endDate, firstDayOfWeek: firstDayOfWeek, hoverDate: _hoverDate, locale: locale, maxDate: _maxDate, minDate: _minDate, onDayClick: function (date) { return handleDayClick(date, index); }, onDayKeyDown: function (event, date) { return handleDayKeyDown(event, date, index); }, onDayMouseEnter: handleDayMouseEnter, onDayMouseLeave: handleDayMouseLeave, onMonthClick: handleMonthClick, onMonthKeyDown: handleMonthKeyDown, onYearClick: handleYearClick, onYearKeyDown: handleYearKeyDown, selectEndDate: _selectEndDate, selectAdjacementDays: selectAdjacementDays, showAdjacementDays: showAdjacementDays, startDate: _startDate, view: view, weekdayFormat: weekdayFormat }))); })));
});
CCalendar.propTypes = {
    className: PropTypes$1.string,
    calendarDate: PropTypes$1.oneOfType([PropTypes$1.instanceOf(Date), PropTypes$1.string]),
    calendars: PropTypes$1.number,
    dayFormat: PropTypes$1.oneOfType([
        PropTypes$1.func,
        PropTypes$1.oneOf(['2-digit', 'numeric']),
    ]),
    disabledDates: PropTypes$1.array,
    endDate: PropTypes$1.oneOfType([PropTypes$1.instanceOf(Date), PropTypes$1.string]),
    firstDayOfWeek: PropTypes$1.number,
    locale: PropTypes$1.string,
    maxDate: PropTypes$1.oneOfType([PropTypes$1.instanceOf(Date), PropTypes$1.string]),
    minDate: PropTypes$1.oneOfType([PropTypes$1.instanceOf(Date), PropTypes$1.string]),
    navigation: PropTypes$1.bool,
    navNextIcon: PropTypes$1.node,
    navNextDoubleIcon: PropTypes$1.node,
    navPrevIcon: PropTypes$1.node,
    navPrevDoubleIcon: PropTypes$1.node,
    navYearFirst: PropTypes$1.bool,
    range: PropTypes$1.bool,
    selectAdjacementDays: PropTypes$1.bool,
    selectEndDate: PropTypes$1.bool,
    showAdjacementDays: PropTypes$1.bool,
    startDate: PropTypes$1.oneOfType([PropTypes$1.instanceOf(Date), PropTypes$1.string]),
    weekdayFormat: PropTypes$1.oneOfType([
        PropTypes$1.func,
        PropTypes$1.number,
        PropTypes$1.oneOf(['long', 'narrow', 'short']),
    ]),
    onDayHover: PropTypes$1.func,
    onCalendarDateChange: PropTypes$1.func,
    onEndDateChange: PropTypes$1.func,
    onSelectEndChange: PropTypes$1.func,
    onStartDateChange: PropTypes$1.func,
    onViewChanged: PropTypes$1.func,
};
CCalendar.displayName = 'CCalendar';

var CFormFeedback = React$1.forwardRef(function (_a, ref) {
    var _b;
    var children = _a.children, className = _a.className, _c = _a.component, Component = _c === void 0 ? 'div' : _c, invalid = _a.invalid, tooltip = _a.tooltip, valid = _a.valid, rest = __rest$1(_a, ["children", "className", "component", "invalid", "tooltip", "valid"]);
    return (React$1.createElement(Component, __assign$1({ className: classNames$1((_b = {},
            _b["invalid-".concat(tooltip ? 'tooltip' : 'feedback')] = invalid,
            _b["valid-".concat(tooltip ? 'tooltip' : 'feedback')] = valid,
            _b), className) }, rest, { ref: ref }), children));
});
CFormFeedback.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    component: PropTypes$1.elementType,
    invalid: PropTypes$1.bool,
    tooltip: PropTypes$1.bool,
    valid: PropTypes$1.bool,
};
CFormFeedback.displayName = 'CFormFeedback';

var CFormControlValidation = function (_a) {
    var describedby = _a.describedby, feedback = _a.feedback, feedbackInvalid = _a.feedbackInvalid, feedbackValid = _a.feedbackValid, invalid = _a.invalid, tooltipFeedback = _a.tooltipFeedback, valid = _a.valid;
    return (React$1.createElement(React$1.Fragment, null,
        feedback && (valid || invalid) && (React$1.createElement(CFormFeedback, __assign$1({}, (invalid && { id: describedby }), { invalid: invalid, tooltip: tooltipFeedback, valid: valid }), feedback)),
        feedbackInvalid && (React$1.createElement(CFormFeedback, { id: describedby, invalid: true, tooltip: tooltipFeedback }, feedbackInvalid)),
        feedbackValid && (React$1.createElement(CFormFeedback, { valid: true, tooltip: tooltipFeedback }, feedbackValid))));
};
CFormControlValidation.propTypes = {
    describedby: PropTypes$1.string,
    feedback: PropTypes$1.oneOfType([PropTypes$1.node, PropTypes$1.string]),
    feedbackValid: PropTypes$1.oneOfType([PropTypes$1.node, PropTypes$1.string]),
    feedbackInvalid: PropTypes$1.oneOfType([PropTypes$1.node, PropTypes$1.string]),
    invalid: PropTypes$1.bool,
    tooltipFeedback: PropTypes$1.bool,
    valid: PropTypes$1.bool,
};
CFormControlValidation.displayName = 'CFormControlValidation';

var CFormFloating = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, rest = __rest$1(_a, ["children", "className"]);
    return (React$1.createElement("div", __assign$1({ className: classNames$1('form-floating', className) }, rest, { ref: ref }), children));
});
CFormFloating.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
};
CFormFloating.displayName = 'CFormFloating';

var CFormLabel = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, customClassName = _a.customClassName, rest = __rest$1(_a, ["children", "className", "customClassName"]);
    return (React$1.createElement("label", __assign$1({ className: customClassName !== null && customClassName !== void 0 ? customClassName : classNames$1('form-label', className) }, rest, { ref: ref }), children));
});
CFormLabel.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    customClassName: PropTypes$1.string,
};
CFormLabel.displayName = 'CFormLabel';

var CFormText = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, _b = _a.component, Component = _b === void 0 ? 'div' : _b, rest = __rest$1(_a, ["children", "className", "component"]);
    return (React$1.createElement(Component, __assign$1({ className: classNames$1('form-text', className) }, rest, { ref: ref }), children));
});
CFormText.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    component: PropTypes$1.elementType,
};
CFormText.displayName = 'CFormText';

var CFormControlWrapper = function (_a) {
    var children = _a.children, describedby = _a.describedby, feedback = _a.feedback, feedbackInvalid = _a.feedbackInvalid, feedbackValid = _a.feedbackValid, floatingClassName = _a.floatingClassName, floatingLabel = _a.floatingLabel, id = _a.id, invalid = _a.invalid, label = _a.label, text = _a.text, tooltipFeedback = _a.tooltipFeedback, valid = _a.valid;
    var FormControlValidation = function () { return (React$1.createElement(CFormControlValidation, { describedby: describedby, feedback: feedback, feedbackInvalid: feedbackInvalid, feedbackValid: feedbackValid, floatingLabel: floatingLabel, invalid: invalid, tooltipFeedback: tooltipFeedback, valid: valid })); };
    return floatingLabel ? (React$1.createElement(CFormFloating, { className: floatingClassName },
        children,
        React$1.createElement(CFormLabel, { htmlFor: id }, label || floatingLabel),
        text && React$1.createElement(CFormText, { id: describedby }, text),
        React$1.createElement(FormControlValidation, null))) : (React$1.createElement(React$1.Fragment, null,
        label && React$1.createElement(CFormLabel, { htmlFor: id }, label),
        children,
        text && React$1.createElement(CFormText, { id: describedby }, text),
        React$1.createElement(FormControlValidation, null)));
};
CFormControlWrapper.propTypes = __assign$1({ children: PropTypes$1.node, floatingClassName: PropTypes$1.string, floatingLabel: PropTypes$1.oneOfType([PropTypes$1.node, PropTypes$1.string]), label: PropTypes$1.oneOfType([PropTypes$1.node, PropTypes$1.string]), text: PropTypes$1.oneOfType([PropTypes$1.node, PropTypes$1.string]) }, CFormControlValidation.propTypes);
CFormControlWrapper.displayName = 'CFormControlWrapper';

var CPicker = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, _b = _a.container, container = _b === void 0 ? 'dropdown' : _b, disabled = _a.disabled, dropdownClassNames = _a.dropdownClassNames, footer = _a.footer, footerContent = _a.footerContent, onHide = _a.onHide, onShow = _a.onShow, toggler = _a.toggler, visible = _a.visible;
    var pickerRef = React$1.useRef(null);
    var pickerForkedRef = useForkedRef(ref, pickerRef);
    var dropdownRef = React$1.useRef(null);
    var togglerRef = React$1.useRef(null);
    var _c = usePopper(), initPopper = _c.initPopper, destroyPopper = _c.destroyPopper;
    var _d = React$1.useState(visible), _visible = _d[0], setVisible = _d[1];
    var popperConfig = {
        placement: (isRTL(pickerRef.current) ? 'bottom-end' : 'bottom-start'),
        modifiers: [
            {
                name: 'preventOverflow',
                options: {
                    boundary: 'clippingParents',
                },
            },
            {
                name: 'offset',
                options: {
                    offset: [0, 2],
                },
            },
        ],
    };
    React$1.useEffect(function () {
        setVisible(visible);
    }, [visible]);
    React$1.useEffect(function () {
        if (container !== 'inline' && _visible) {
            onShow && onShow();
            window.addEventListener('mouseup', handleMouseUp);
            window.addEventListener('keyup', handleKeyUp);
            togglerRef.current &&
                dropdownRef.current &&
                initPopper(togglerRef.current, dropdownRef.current, popperConfig);
        }
        return function () {
            onHide && onHide();
            window.removeEventListener('mouseup', handleMouseUp);
            window.removeEventListener('keyup', handleKeyUp);
            destroyPopper();
        };
    }, [_visible]);
    var handleKeyUp = function (event) {
        if (event.key === 'Escape') {
            setVisible(false);
        }
    };
    var handleMouseUp = function (event) {
        if (pickerRef.current && pickerRef.current.contains(event.target)) {
            return;
        }
        setVisible(false);
    };
    switch (container) {
        case 'inline': {
            return (React$1.createElement("div", { className: classNames$1('picker', className), ref: pickerForkedRef }, children));
        }
        default: {
            return (React$1.createElement("div", { className: classNames$1('dropdown', 'picker', className, {
                    show: _visible,
                }), onClick: function () { return !disabled && setVisible(true); }, ref: pickerForkedRef },
                toggler &&
                    React$1.isValidElement(toggler) &&
                    React$1.cloneElement(toggler, {
                        ref: togglerRef,
                    }),
                React$1.createElement("div", { className: classNames$1('dropdown-menu', {
                        show: _visible,
                    }, dropdownClassNames), ref: dropdownRef },
                    children,
                    footer && footerContent)));
        }
    }
});
CPicker.displayName = 'CPicker';
CPicker.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    container: PropTypes$1.oneOf(['dropdown', 'inline']),
    disabled: PropTypes$1.bool,
    dropdownClassNames: PropTypes$1.string,
    footer: PropTypes$1.oneOfType([PropTypes$1.bool, PropTypes$1.node]),
    footerContent: PropTypes$1.node,
    onHide: PropTypes$1.func,
    onShow: PropTypes$1.func,
    toggler: PropTypes$1.node,
};

var CTimePickerRollCol = React$1.forwardRef(function (_a, ref) {
    var elements = _a.elements, onClick = _a.onClick, selected = _a.selected;
    var init = React$1.useRef(true);
    var colRef = React$1.useRef(null);
    var forkedRef = useForkedRef(ref, colRef);
    var isVisible = useIsVisible(colRef);
    React$1.useEffect(function () {
        var _a, _b;
        var nodeEl = (_a = colRef.current) === null || _a === void 0 ? void 0 : _a.querySelector('.selected');
        if (isVisible && nodeEl && nodeEl instanceof HTMLElement) {
            (_b = colRef.current) === null || _b === void 0 ? void 0 : _b.scrollTo({
                top: nodeEl.offsetTop,
                behavior: init.current ? 'auto' : 'smooth',
            });
        }
        if (isVisible) {
            init.current = false;
        }
    }, [isVisible, selected]);
    var handleKeyDown = function (event, value) {
        if (event.code === 'Space' || event.key === 'Enter') {
            event.preventDefault();
            onClick && onClick(value);
        }
    };
    return (React$1.createElement("div", { className: "time-picker-roll-col", ref: forkedRef }, elements.map(function (element, index) {
        return (React$1.createElement("div", { className: classNames$1('time-picker-roll-cell', {
                selected: element.value === selected,
            }), key: index, onClick: function () { return onClick && onClick(element.value); }, onKeyDown: function (event) { return handleKeyDown(event, element.value); }, role: "button", tabIndex: 0 }, element.label));
    })));
});
CTimePickerRollCol.propTypes = {
    elements: PropTypes$1.array.isRequired,
    onClick: PropTypes$1.func,
    selected: PropTypes$1.oneOfType([PropTypes$1.number, PropTypes$1.string]),
};
CTimePickerRollCol.displayName = 'CTimePickerRollCol';

var convert12hTo24h = function (abbr, hour) {
    if (abbr === 'am' && hour === 12) {
        return 0;
    }
    if (abbr === 'am') {
        return hour;
    }
    if (abbr === 'pm' && hour === 12) {
        return 12;
    }
    return hour + 12;
};
var convert24hTo12h = function (hour) { return hour % 12 || 12; };
var convertTimeToDate = function (time) {
    return time ? (time instanceof Date ? new Date(time) : new Date("1970-01-01 ".concat(time))) : null;
};
var getAmPm = function (date, locale) {
    if (date.toLocaleTimeString(locale).includes('AM')) {
        return 'am';
    }
    if (date.toLocaleTimeString(locale).includes('PM')) {
        return 'pm';
    }
    return date.getHours() >= 12 ? 'pm' : 'am';
};
var getLocalizedTimePartials = function (locale, ampm) {
    if (ampm === void 0) { ampm = 'auto'; }
    var date = new Date();
    var hour12 = ['am', 'AM', 'pm', 'PM'].some(function (el) { return date.toLocaleString(locale).includes(el); });
    var listOfHours = Array.from({ length: (ampm === 'auto' && hour12) || ampm === true ? 12 : 24 }, function (_, i) {
        return {
            value: (ampm === 'auto' && hour12) || ampm === true ? i + 1 : i,
            label: ((ampm === 'auto' && hour12) || ampm === true ? i + 1 : i).toLocaleString(locale),
        };
    });
    var listOfMinutesSeconds = Array.from({ length: 60 }, function (_, i) {
        date.setMinutes(i);
        return {
            value: i,
            label: date
                .toLocaleTimeString(locale, {
                minute: '2-digit',
                second: '2-digit',
            })
                .split(/[^A-Za-z0-9\u06F0-\u06F90-9]/)[0],
        };
    });
    return {
        listOfHours: listOfHours,
        listOfMinutes: listOfMinutesSeconds,
        listOfSeconds: listOfMinutesSeconds,
        hour12: hour12,
    };
};
var getSelectedHour = function (date, locale, ampm) {
    if (ampm === void 0) { ampm = 'auto'; }
    return date
        ? (ampm === 'auto' && isAmPm(locale)) || ampm === true
            ? convert24hTo12h(date.getHours())
            : date.getHours()
        : '';
};
var getSelectedMinutes = function (date) { return (date ? date.getMinutes() : ''); };
var getSelectedSeconds = function (date) { return (date ? date.getSeconds() : ''); };
var isAmPm = function (locale) {
    return ['am', 'AM', 'pm', 'PM'].some(function (el) { return new Date().toLocaleString(locale).includes(el); });
};
var isValidTime = function (time) {
    var d = new Date("1970-01-01 ".concat(time));
    return d instanceof Date && d.getTime();
};

var _a$1, _b$1, _c$1, _d$1, _e$1, _f$1;
var CTimePicker = React$1.forwardRef(function (_a, ref) {
    var _b, _c;
    var _d = _a.ampm, ampm = _d === void 0 ? 'auto' : _d, _e = _a.cancelButton, cancelButton = _e === void 0 ? 'Cancel' : _e, _f = _a.cancelButtonColor, cancelButtonColor = _f === void 0 ? 'primary' : _f, _g = _a.cancelButtonSize, cancelButtonSize = _g === void 0 ? 'sm' : _g, _h = _a.cancelButtonVariant, cancelButtonVariant = _h === void 0 ? 'ghost' : _h, className = _a.className, _j = _a.cleaner, cleaner = _j === void 0 ? true : _j, _k = _a.confirmButton, confirmButton = _k === void 0 ? 'OK' : _k, _l = _a.confirmButtonColor, confirmButtonColor = _l === void 0 ? 'primary' : _l, _m = _a.confirmButtonSize, confirmButtonSize = _m === void 0 ? 'sm' : _m, confirmButtonVariant = _a.confirmButtonVariant, _o = _a.container, container = _o === void 0 ? 'dropdown' : _o, disabled = _a.disabled, feedback = _a.feedback, feedbackInvalid = _a.feedbackInvalid, feedbackValid = _a.feedbackValid, _p = _a.footer, footer = _p === void 0 ? true : _p, id = _a.id, _q = _a.indicator, indicator = _q === void 0 ? true : _q, inputReadOnly = _a.inputReadOnly, invalid = _a.invalid, label = _a.label, _r = _a.locale, locale = _r === void 0 ? 'default' : _r, onTimeChange = _a.onTimeChange, onHide = _a.onHide, onShow = _a.onShow, _s = _a.placeholder, placeholder = _s === void 0 ? 'Select time' : _s, required = _a.required, _t = _a.seconds, seconds = _t === void 0 ? true : _t, size = _a.size, text = _a.text, time = _a.time, tooltipFeedback = _a.tooltipFeedback, valid = _a.valid, _u = _a.variant, variant = _u === void 0 ? 'roll' : _u, visible = _a.visible, rest = __rest$1(_a, ["ampm", "cancelButton", "cancelButtonColor", "cancelButtonSize", "cancelButtonVariant", "className", "cleaner", "confirmButton", "confirmButtonColor", "confirmButtonSize", "confirmButtonVariant", "container", "disabled", "feedback", "feedbackInvalid", "feedbackValid", "footer", "id", "indicator", "inputReadOnly", "invalid", "label", "locale", "onTimeChange", "onHide", "onShow", "placeholder", "required", "seconds", "size", "text", "time", "tooltipFeedback", "valid", "variant", "visible"]);
    var formRef = React$1.useRef();
    var inputRef = React$1.useRef(null);
    var _v = React$1.useState(convertTimeToDate(time)), date = _v[0], setDate = _v[1];
    var _w = React$1.useState(null), initialDate = _w[0], setInitialDate = _w[1];
    var _x = React$1.useState(valid !== null && valid !== void 0 ? valid : (invalid === true ? false : undefined)), isValid = _x[0], setIsValid = _x[1];
    var _y = React$1.useState(date ? getAmPm(new Date(date), locale) : 'am'), _ampm = _y[0], setAmPm = _y[1];
    var _z = React$1.useState(visible), _visible = _z[0], setVisible = _z[1];
    var _0 = React$1.useState({
        listOfHours: [],
        listOfMinutes: [],
        listOfSeconds: [],
        hour12: false,
    }), localizedTimePartials = _0[0], setLocalizedTimePartials = _0[1];
    React$1.useEffect(function () {
        setDate(time ? convertTimeToDate(time) : null);
    }, [time]);
    React$1.useEffect(function () {
        setIsValid(valid !== null && valid !== void 0 ? valid : (invalid === true ? false : undefined));
    }, [valid, invalid]);
    React$1.useEffect(function () {
        setLocalizedTimePartials(getLocalizedTimePartials(locale, ampm));
        if (inputRef.current) {
            inputRef.current.value = date
                ? date.toLocaleTimeString(locale, __assign$1({ hour12: localizedTimePartials && localizedTimePartials.hour12 }, (!seconds && { timeStyle: 'short' })))
                : '';
        }
        date && setAmPm(getAmPm(new Date(date), locale));
    }, [date]);
    React$1.useEffect(function () {
        if (inputRef.current && inputRef.current.form) {
            formRef.current = inputRef.current.form;
        }
    }, [inputRef]);
    React$1.useEffect(function () {
        if (formRef.current) {
            formRef.current.addEventListener('submit', function (event) {
                setTimeout(function () { return handleFormValidation(event.target); });
            });
            handleFormValidation(formRef.current);
        }
    }, [formRef, date]);
    var handleClear = function (event) {
        event.stopPropagation();
        setDate(null);
        onTimeChange && onTimeChange(null);
    };
    var handleFormValidation = function (form) {
        if (!form.classList.contains('was-validated')) {
            return;
        }
        if (date) {
            return setIsValid(true);
        }
        setIsValid(false);
    };
    var handleTimeChange = function (set, value) {
        var _date = date || new Date('1970-01-01');
        if (set === 'toggle') {
            if (value === 'am') {
                _date.setHours(_date.getHours() - 12);
            }
            if (value === 'pm') {
                _date.setHours(_date.getHours() + 12);
            }
        }
        if (set === 'hours') {
            if (localizedTimePartials && localizedTimePartials.hour12) {
                _date.setHours(convert12hTo24h(_ampm, Number.parseInt(value)));
            }
            else {
                _date.setHours(Number.parseInt(value));
            }
        }
        if (set === 'minutes') {
            _date.setMinutes(Number.parseInt(value));
        }
        if (set === 'seconds') {
            _date.setSeconds(Number.parseInt(value));
        }
        setDate(new Date(_date));
        onTimeChange && onTimeChange(_date.toTimeString(), _date.toLocaleTimeString(), _date);
    };
    var InputGroup = function () {
        var _a;
        return (React$1.createElement("div", { className: classNames$1('input-group', 'picker-input-group', (_a = {},
                _a["input-group-".concat(size)] = size,
                _a)) },
            React$1.createElement("input", { autoComplete: "off", className: "form-control", disabled: disabled, onChange: function (event) {
                    return isValidTime(event.target.value) && setDate(convertTimeToDate(event.target.value));
                }, placeholder: placeholder, readOnly: inputReadOnly, required: required, ref: inputRef }),
            (indicator || cleaner) && (React$1.createElement("span", { className: "input-group-text" },
                indicator && (React$1.createElement("span", { className: "picker-input-group-indicator" }, typeof indicator === 'boolean' ? (React$1.createElement("span", { className: "picker-input-group-icon time-picker-input-icon" })) : (indicator))),
                cleaner && date && (React$1.createElement("span", { className: "picker-input-group-cleaner", role: "button", onClick: function (event) { return handleClear(event); } }, typeof cleaner === 'boolean' ? (React$1.createElement("span", { className: "picker-input-group-icon time-picker-cleaner-icon" })) : (cleaner)))))));
    };
    var TimePickerSelect = function () {
        return (React$1.createElement(React$1.Fragment, null,
            React$1.createElement("span", { className: "time-picker-inline-icon" }),
            React$1.createElement("select", { className: "form-select", disabled: disabled, onChange: function (event) {
                    return handleTimeChange('hours', event.target.value);
                }, value: getSelectedHour(date, locale) }, localizedTimePartials &&
                localizedTimePartials.listOfHours.map(function (option, index) { return (React$1.createElement("option", { value: option.value.toString(), key: index }, option.label)); })),
            React$1.createElement(React$1.Fragment, null, ":"),
            React$1.createElement("select", { className: "form-select", disabled: disabled, onChange: function (event) {
                    return handleTimeChange('minutes', event.target.value);
                }, value: getSelectedMinutes(date) }, localizedTimePartials &&
                localizedTimePartials.listOfMinutes.map(function (option, index) { return (React$1.createElement("option", { value: option.value.toString(), key: index }, option.label)); })),
            seconds && (React$1.createElement(React$1.Fragment, null,
                React$1.createElement(React$1.Fragment, null, ":"),
                React$1.createElement("select", { className: "form-select", disabled: disabled, onChange: function (event) {
                        return handleTimeChange('seconds', event.target.value);
                    }, value: getSelectedSeconds(date) }, localizedTimePartials &&
                    localizedTimePartials.listOfSeconds.map(function (option, index) { return (React$1.createElement("option", { value: option.value.toString(), key: index }, option.label)); })))),
            localizedTimePartials && localizedTimePartials.hour12 && (React$1.createElement("select", { className: "form-select", disabled: disabled, onChange: function (event) {
                    return handleTimeChange('toggle', event.target.value);
                }, value: _ampm },
                React$1.createElement("option", { value: "am" }, "AM"),
                React$1.createElement("option", { value: "pm" }, "PM")))));
    };
    return (React$1.createElement(CFormControlWrapper, { describedby: rest['aria-describedby'], feedback: feedback, feedbackInvalid: feedbackInvalid, feedbackValid: feedbackValid, id: id, invalid: isValid === false ? true : false, label: label, text: text, tooltipFeedback: tooltipFeedback, valid: isValid },
        React$1.createElement(CPicker, __assign$1({ className: classNames$1('time-picker', (_b = {},
                _b["time-picker-".concat(size)] = size,
                _b.disabled = disabled,
                _b['is-invalid'] = isValid === false ? true : false,
                _b['is-valid'] = isValid,
                _b), className), container: container, disabled: disabled, dropdownClassNames: "time-picker-dropdown", footer: footer, footerContent: React$1.createElement("div", { className: "picker-footer" },
                cancelButton && (React$1.createElement(CButton, { color: cancelButtonColor, size: cancelButtonSize, variant: cancelButtonVariant, onClick: function () {
                        initialDate && setDate(new Date(initialDate));
                        setVisible(false);
                    } }, cancelButton)),
                confirmButton && (React$1.createElement(CButton, { color: confirmButtonColor, size: confirmButtonSize, variant: confirmButtonVariant, onClick: function () {
                        setVisible(false);
                    } }, confirmButton))), id: id, onHide: function () {
                setVisible(false);
                onHide && onHide();
            }, onShow: function () {
                date && setInitialDate(new Date(date));
                setVisible(true);
                onShow && onShow();
            }, toggler: InputGroup(), visible: _visible }, rest, { ref: ref }),
            React$1.createElement("div", { className: classNames$1('time-picker-body', (_c = {},
                    _c['time-picker-roll'] = variant === 'roll',
                    _c)) }, variant === 'select' ? (React$1.createElement(TimePickerSelect, null)) : (React$1.createElement(React$1.Fragment, null,
                React$1.createElement(CTimePickerRollCol, { elements: localizedTimePartials && localizedTimePartials.listOfHours, onClick: function (index) { return handleTimeChange('hours', index.toString()); }, selected: getSelectedHour(date, locale, ampm) }),
                React$1.createElement(CTimePickerRollCol, { elements: localizedTimePartials && localizedTimePartials.listOfMinutes, onClick: function (index) { return handleTimeChange('minutes', index.toString()); }, selected: getSelectedMinutes(date) }),
                seconds && (React$1.createElement(CTimePickerRollCol, { elements: localizedTimePartials && localizedTimePartials.listOfSeconds, onClick: function (index) { return handleTimeChange('seconds', index.toString()); }, selected: getSelectedSeconds(date) })),
                localizedTimePartials && localizedTimePartials.hour12 && (React$1.createElement(CTimePickerRollCol, { elements: [
                        { value: 'am', label: 'AM' },
                        { value: 'pm', label: 'PM' },
                    ], onClick: function (value) { return handleTimeChange('toggle', value); }, selected: _ampm }))))))));
});
CTimePicker.propTypes = __assign$1(__assign$1(__assign$1({}, CFormControlWrapper.propTypes), CPicker.propTypes), { ampm: PropTypes$1.oneOfType([PropTypes$1.oneOf(['auto']), PropTypes$1.bool]), cancelButton: PropTypes$1.oneOfType([PropTypes$1.bool, PropTypes$1.node]), cancelButtonColor: (_a$1 = CButton.propTypes) === null || _a$1 === void 0 ? void 0 : _a$1.color, cancelButtonSize: (_b$1 = CButton.propTypes) === null || _b$1 === void 0 ? void 0 : _b$1.size, cancelButtonVariant: (_c$1 = CButton.propTypes) === null || _c$1 === void 0 ? void 0 : _c$1.variant, className: PropTypes$1.string, confirmButton: PropTypes$1.oneOfType([PropTypes$1.bool, PropTypes$1.node]), confirmButtonColor: (_d$1 = CButton.propTypes) === null || _d$1 === void 0 ? void 0 : _d$1.color, confirmButtonSize: (_e$1 = CButton.propTypes) === null || _e$1 === void 0 ? void 0 : _e$1.size, confirmButtonVariant: (_f$1 = CButton.propTypes) === null || _f$1 === void 0 ? void 0 : _f$1.variant, locale: PropTypes$1.string, onTimeChange: PropTypes$1.func, required: PropTypes$1.bool, seconds: PropTypes$1.bool, time: PropTypes$1.oneOfType([PropTypes$1.instanceOf(Date), PropTypes$1.string]), variant: PropTypes$1.oneOf(['roll', 'select']) });
CTimePicker.displayName = 'CTimePicker';

var getLocalDateFromString = function (string, locale, time) {
    if (!Number.isNaN(Date.parse(string))) {
        return new Date(Date.parse(string));
    }
    var date = new Date(2013, 11, 31, 17, 19, 22);
    var regex = time ? date.toLocaleString(locale) : date.toLocaleDateString(locale);
    regex = regex
        .replace('2013', '(?<year>[0-9]{2,4})')
        .replace('12', '(?<month>[0-9]{1,2})')
        .replace('31', '(?<day>[0-9]{1,2})');
    if (time) {
        regex = regex
            .replace('5', '(?<hour>[0-9]{1,2})')
            .replace('17', '(?<hour>[0-9]{1,2})')
            .replace('19', '(?<minute>[0-9]{1,2})')
            .replace('22', '(?<second>[0-9]{1,2})')
            .replace('PM', '(?<ampm>[A-Z]{2})');
    }
    var rgx = new RegExp("".concat(regex));
    var partials = string.match(rgx);
    if (partials === null)
        return;
    var newDate = partials.groups &&
        (time
            ? new Date(Number(partials.groups['year']), Number(partials.groups['month']) - 1, Number(partials.groups['day']), partials.groups['ampm']
                ? (partials.groups['ampm'] === 'PM'
                    ? Number(partials.groups['hour']) + 12
                    : Number(partials.groups['hour']))
                : Number(partials.groups['hour']), Number(partials.groups['minute']), Number(partials.groups['second']))
            : new Date(Number(partials.groups['year']), Number(partials.groups['month']) - 1, Number(partials.groups['day'])));
    return newDate;
};

var _a, _b, _c, _d, _e, _f, _g, _h, _j, _k, _l, _m;
var CDateRangePicker = React$1.forwardRef(function (_a, ref) {
    var _b;
    var _c = _a.calendars, calendars = _c === void 0 ? 2 : _c, calendarDate = _a.calendarDate, _d = _a.cancelButton, cancelButton = _d === void 0 ? 'Cancel' : _d, _e = _a.cancelButtonColor, cancelButtonColor = _e === void 0 ? 'primary' : _e, _f = _a.cancelButtonSize, cancelButtonSize = _f === void 0 ? 'sm' : _f, _g = _a.cancelButtonVariant, cancelButtonVariant = _g === void 0 ? 'ghost' : _g, className = _a.className, _h = _a.cleaner, cleaner = _h === void 0 ? true : _h, _j = _a.closeOnSelect, closeOnSelect = _j === void 0 ? true : _j, _k = _a.confirmButton, confirmButton = _k === void 0 ? 'OK' : _k, _l = _a.confirmButtonColor, confirmButtonColor = _l === void 0 ? 'primary' : _l, _m = _a.confirmButtonSize, confirmButtonSize = _m === void 0 ? 'sm' : _m, confirmButtonVariant = _a.confirmButtonVariant, dayFormat = _a.dayFormat, disabled = _a.disabled, disabledDates = _a.disabledDates, endDate = _a.endDate, feedback = _a.feedback, feedbackInvalid = _a.feedbackInvalid, feedbackValid = _a.feedbackValid, firstDayOfWeek = _a.firstDayOfWeek, format$1 = _a.format, footer = _a.footer, id = _a.id, _o = _a.indicator, indicator = _o === void 0 ? true : _o, inputDateFormat = _a.inputDateFormat, inputDateParse = _a.inputDateParse, _p = _a.inputOnChangeDelay, inputOnChangeDelay = _p === void 0 ? 750 : _p, inputReadOnly = _a.inputReadOnly, invalid = _a.invalid, label = _a.label, _q = _a.locale, locale = _q === void 0 ? 'default' : _q, maxDate = _a.maxDate, minDate = _a.minDate, navigation = _a.navigation, navYearFirst = _a.navYearFirst, onEndDateChange = _a.onEndDateChange, onHide = _a.onHide, onStartDateChange = _a.onStartDateChange, onShow = _a.onShow, _r = _a.placeholder, placeholder = _r === void 0 ? ['Start date', 'End date'] : _r, _s = _a.range, range = _s === void 0 ? true : _s, ranges = _a.ranges, _t = _a.rangesButtonsColor, rangesButtonsColor = _t === void 0 ? 'secondary' : _t, rangesButtonsSize = _a.rangesButtonsSize, _u = _a.rangesButtonsVariant, rangesButtonsVariant = _u === void 0 ? 'ghost' : _u, required = _a.required, _v = _a.separator, separator = _v === void 0 ? true : _v, selectAdjacementDays = _a.selectAdjacementDays, showAdjacementDays = _a.showAdjacementDays, size = _a.size, startDate = _a.startDate, text = _a.text, timepicker = _a.timepicker, toggler = _a.toggler, _w = _a.todayButton, todayButton = _w === void 0 ? 'Today' : _w, _x = _a.todayButtonColor, todayButtonColor = _x === void 0 ? 'primary' : _x, _y = _a.todayButtonSize, todayButtonSize = _y === void 0 ? 'sm' : _y, todayButtonVariant = _a.todayButtonVariant, tooltipFeedback = _a.tooltipFeedback, valid = _a.valid, visible = _a.visible, weekdayFormat = _a.weekdayFormat, rest = __rest$1(_a, ["calendars", "calendarDate", "cancelButton", "cancelButtonColor", "cancelButtonSize", "cancelButtonVariant", "className", "cleaner", "closeOnSelect", "confirmButton", "confirmButtonColor", "confirmButtonSize", "confirmButtonVariant", "dayFormat", "disabled", "disabledDates", "endDate", "feedback", "feedbackInvalid", "feedbackValid", "firstDayOfWeek", "format", "footer", "id", "indicator", "inputDateFormat", "inputDateParse", "inputOnChangeDelay", "inputReadOnly", "invalid", "label", "locale", "maxDate", "minDate", "navigation", "navYearFirst", "onEndDateChange", "onHide", "onStartDateChange", "onShow", "placeholder", "range", "ranges", "rangesButtonsColor", "rangesButtonsSize", "rangesButtonsVariant", "required", "separator", "selectAdjacementDays", "showAdjacementDays", "size", "startDate", "text", "timepicker", "toggler", "todayButton", "todayButtonColor", "todayButtonSize", "todayButtonVariant", "tooltipFeedback", "valid", "visible", "weekdayFormat"]);
    var inputEndRef = React$1.useRef(null);
    var inputStartRef = React$1.useRef(null);
    var formRef = React$1.useRef();
    var _z = React$1.useState(calendarDate ? new Date(calendarDate) : new Date()), _calendarDate = _z[0], setCalendarDate = _z[1];
    var _0 = React$1.useState(endDate ? new Date(endDate) : null), _endDate = _0[0], setEndDate = _0[1];
    var _1 = React$1.useState(maxDate ? new Date(maxDate) : null), _maxDate = _1[0], setMaxDate = _1[1];
    var _2 = React$1.useState(minDate ? new Date(minDate) : null), _minDate = _2[0], setMinDate = _2[1];
    var _3 = React$1.useState(startDate ? new Date(startDate) : null), _startDate = _3[0], setStartDate = _3[1];
    var _4 = React$1.useState(visible), _visible = _4[0], setVisible = _4[1];
    var _5 = React$1.useState(startDate ? new Date(startDate) : null), initialStartDate = _5[0], setInitialStartDate = _5[1];
    var _6 = React$1.useState(endDate ? new Date(endDate) : null), initialEndDate = _6[0], setInitialEndDate = _6[1];
    var _7 = React$1.useState(null), inputStartHoverValue = _7[0], setInputStartHoverValue = _7[1];
    var _8 = React$1.useState(null), inputEndHoverValue = _8[0], setInputEndHoverValue = _8[1];
    var _9 = React$1.useState(valid !== null && valid !== void 0 ? valid : (invalid === true ? false : undefined)), isValid = _9[0], setIsValid = _9[1];
    var _10 = React$1.useState(false), selectEndDate = _10[0], setSelectEndDate = _10[1];
    React$1.useEffect(function () {
        setIsValid(valid !== null && valid !== void 0 ? valid : (invalid === true ? false : undefined));
    }, [valid, invalid]);
    React$1.useEffect(function () {
        setStartDate(startDate ? new Date(startDate) : null);
        setCalendarDate(startDate ? new Date(startDate) : new Date());
    }, [startDate]);
    React$1.useEffect(function () {
        setEndDate(endDate ? new Date(endDate) : null);
        range && setCalendarDate(endDate ? new Date(endDate) : new Date());
    }, [endDate]);
    React$1.useEffect(function () {
        maxDate && setMaxDate(new Date(maxDate));
    }, [maxDate]);
    React$1.useEffect(function () {
        minDate && setMinDate(new Date(minDate));
    }, [minDate]);
    React$1.useEffect(function () {
        if (inputStartHoverValue) {
            setInputValue(inputStartRef.current, inputStartHoverValue);
            return;
        }
        setInputValue(inputStartRef.current, _startDate);
    }, [inputStartHoverValue, _startDate]);
    React$1.useEffect(function () {
        if (inputEndHoverValue) {
            setInputValue(inputEndRef.current, inputEndHoverValue);
            return;
        }
        setInputValue(inputEndRef.current, _endDate);
    }, [inputEndHoverValue, _endDate]);
    React$1.useEffect(function () {
        if (inputStartRef.current && inputStartRef.current.form) {
            formRef.current = inputStartRef.current.form;
        }
    }, [inputStartRef]);
    React$1.useEffect(function () {
        if (formRef.current) {
            formRef.current.addEventListener('submit', function (event) {
                setTimeout(function () { return handleFormValidation(event.target); });
            });
            handleFormValidation(formRef.current);
        }
    }, [formRef, _startDate, _endDate]);
    var formatDate = function (date) {
        return inputDateFormat
            ? inputDateFormat(date)
            : format$1
                ? format(date, format$1)
                : timepicker
                    ? date.toLocaleString(locale)
                    : date.toLocaleDateString(locale);
    };
    var setInputValue = function (el, date) {
        if (!el) {
            return;
        }
        if (date) {
            el.value = formatDate(date);
            return;
        }
        el.value = '';
    };
    var handleDayHover = function (date) {
        selectEndDate ? setInputEndHoverValue(date) : setInputStartHoverValue(date);
    };
    var handleCalendarDateChange = function (date, difference) {
        difference
            ? setCalendarDate(new Date(date.getFullYear(), date.getMonth() - difference, 1))
            : setCalendarDate(date);
    };
    var handleClear = function (event) {
        event.stopPropagation();
        setStartDate(null);
        setEndDate(null);
    };
    var handleEndDateChange = function (date) {
        setEndDate(date);
        setInputEndHoverValue(null);
        onEndDateChange && onEndDateChange(date, date ? formatDate(date) : undefined);
        if (timepicker || footer) {
            return;
        }
        if (closeOnSelect) {
            _startDate !== null && setVisible(false);
        }
    };
    var handleFormValidation = function (form) {
        if (!form.classList.contains('was-validated')) {
            return;
        }
        if ((range && _startDate && _endDate) || (!range && _startDate)) {
            return setIsValid(true);
        }
        setIsValid(false);
    };
    var handleStartDateChange = function (date) {
        setStartDate(date);
        setInputStartHoverValue(null);
        onStartDateChange && onStartDateChange(date, date ? formatDate(date) : undefined);
        if (timepicker || footer) {
            return;
        }
        if (closeOnSelect && !range) {
            setVisible(false);
        }
    };
    var handleOnChange = useDebouncedCallback(function (value, input) {
        var date = inputDateParse
            ? inputDateParse(value)
            : getLocalDateFromString(value, locale, timepicker);
        if (date instanceof Date && date.getTime()) {
            setCalendarDate(date);
            input === 'start' ? setStartDate(date) : setEndDate(date);
        }
    }, inputOnChangeDelay);
    var InputGroup = function () {
        var _a;
        return (React$1.createElement("div", { className: classNames$1('input-group', 'picker-input-group', (_a = {},
                _a["input-group-".concat(size)] = size,
                _a)) },
            React$1.createElement("input", __assign$1({ autoComplete: "off", className: classNames$1('form-control date-picker-input', {
                    hover: inputStartHoverValue,
                }), disabled: disabled }, (id && { name: range ? "".concat(id, "-start-date") : "".concat(id, "-date") }), { placeholder: Array.isArray(placeholder) ? placeholder[0] : placeholder, readOnly: inputReadOnly || typeof format$1 === 'string', required: required, onChange: function (event) {
                    handleOnChange(event.target.value, 'start');
                }, onClick: function () { return setSelectEndDate(false); }, ref: inputStartRef })),
            range && separator !== false && (React$1.createElement("span", { className: "input-group-text" },
                React$1.createElement("span", { className: "picker-input-group-icon date-picker-arrow-icon" }))),
            range && (React$1.createElement("input", __assign$1({ autoComplete: "off", className: classNames$1('form-control date-picker-input', {
                    hover: inputEndHoverValue,
                }), disabled: disabled }, (id && { name: "".concat(id, "-end-date") }), { placeholder: placeholder[1], readOnly: inputReadOnly || typeof format$1 === 'string', required: required, onChange: function (event) {
                    handleOnChange(event.target.value, 'end');
                }, onClick: function () { return setSelectEndDate(true); }, ref: inputEndRef }))),
            (indicator || cleaner) && (React$1.createElement("span", { className: "input-group-text" },
                indicator && (React$1.createElement("span", { className: "picker-input-group-indicator" }, typeof indicator === 'boolean' ? (React$1.createElement("span", { className: "picker-input-group-icon date-picker-input-icon" })) : (indicator))),
                cleaner && (_startDate || _endDate) && (React$1.createElement("span", { className: "picker-input-group-cleaner", role: "button", onClick: function (event) { return handleClear(event); } }, typeof cleaner === 'boolean' ? (React$1.createElement("span", { className: "picker-input-group-icon date-picker-cleaner-icon" })) : (cleaner)))))));
    };
    return (React$1.createElement(CFormControlWrapper, { describedby: rest['aria-describedby'], feedback: feedback, feedbackInvalid: feedbackInvalid, feedbackValid: feedbackValid, id: id, invalid: isValid === false ? true : false, label: label, text: text, tooltipFeedback: tooltipFeedback, valid: isValid },
        React$1.createElement(CPicker, __assign$1({ className: classNames$1('date-picker', (_b = {},
                _b["date-picker-".concat(size)] = size,
                _b.disabled = disabled,
                _b['is-invalid'] = isValid === false ? true : false,
                _b['is-valid'] = isValid,
                _b), className), disabled: disabled, footer: footer || timepicker, footerContent: React$1.createElement("div", { className: "picker-footer" },
                todayButton && (React$1.createElement(CButton, { className: "me-auto", color: todayButtonColor, size: todayButtonSize, variant: todayButtonVariant, onClick: function () {
                        var date = new Date();
                        handleStartDateChange(date);
                        range && handleEndDateChange(date);
                        setCalendarDate(date);
                    } }, todayButton)),
                cancelButton && (React$1.createElement(CButton, { color: cancelButtonColor, size: cancelButtonSize, variant: cancelButtonVariant, onClick: function () {
                        handleStartDateChange(initialStartDate);
                        range && handleEndDateChange(initialEndDate);
                        setVisible(false);
                    } }, cancelButton)),
                confirmButton && (React$1.createElement(CButton, { color: confirmButtonColor, size: confirmButtonSize, variant: confirmButtonVariant, onClick: function () {
                        setVisible(false);
                    } }, confirmButton))), id: id, toggler: toggler !== null && toggler !== void 0 ? toggler : InputGroup(), onHide: function () {
                setVisible(false);
                onHide && onHide();
            }, onShow: function () {
                setInitialStartDate(_startDate);
                setInitialEndDate(_endDate);
                setVisible(true);
                onShow && onShow();
            }, visible: _visible }, rest, { ref: ref }),
            React$1.createElement("div", { className: "date-picker-body" },
                ranges && (React$1.createElement("div", { className: "date-picker-ranges" }, Object.keys(ranges).map(function (key, index) { return (React$1.createElement(CButton, { color: rangesButtonsColor, key: index, onClick: function () {
                        handleStartDateChange(ranges[key][0]);
                        handleEndDateChange(ranges[key][1]);
                    }, size: rangesButtonsSize, variant: rangesButtonsVariant }, key)); }))),
                React$1.createElement(CCalendar, { calendarDate: _calendarDate, calendars: isMobile_1 ? 1 : calendars, className: "date-picker-calendars", dayFormat: dayFormat, disabledDates: disabledDates, endDate: _endDate, firstDayOfWeek: firstDayOfWeek, locale: locale, maxDate: _maxDate, minDate: _minDate, navigation: navigation, navYearFirst: navYearFirst, range: range, selectAdjacementDays: selectAdjacementDays, selectEndDate: selectEndDate, showAdjacementDays: showAdjacementDays, startDate: _startDate, onDayHover: function (date) { return handleDayHover(date); }, onCalendarDateChange: function (date) { return handleCalendarDateChange(date); }, onStartDateChange: function (date) { return handleStartDateChange(date); }, onEndDateChange: function (date) { return handleEndDateChange(date); }, onSelectEndChange: function (value) { return setSelectEndDate(value); }, weekdayFormat: weekdayFormat }),
                timepicker && (React$1.createElement("div", { className: "date-picker-timepickers" }, isMobile_1 || (range && calendars === 1) ? (React$1.createElement(React$1.Fragment, null,
                    React$1.createElement(CTimePicker, { container: "inline", disabled: _startDate === null ? true : false, locale: locale, onTimeChange: function (_, __, date) { return date && handleStartDateChange(date); }, time: _startDate, variant: "select" }),
                    React$1.createElement(CTimePicker, { container: "inline", disabled: _endDate === null ? true : false, locale: locale, onTimeChange: function (_, __, date) { return date && handleEndDateChange(date); }, time: _endDate, variant: "select" }))) : (Array.from({ length: calendars }).map(function (_, index) { return (React$1.createElement(CTimePicker, { container: "inline", disabled: index === 0
                        ? _startDate === null
                            ? true
                            : false
                        : _endDate === null
                            ? true
                            : false, key: index, locale: locale, onTimeChange: function (_, __, date) {
                        return index === 0
                            ? date && handleStartDateChange(date)
                            : date && handleEndDateChange(date);
                    }, time: index === 0 ? _startDate : _endDate, variant: "select" })); }))))))));
});
CDateRangePicker.displayName = 'CDateRangePicker';
CDateRangePicker.propTypes = __assign$1(__assign$1(__assign$1(__assign$1({}, CCalendar.propTypes), CFormControlWrapper.propTypes), CPicker.propTypes), { cancelButton: PropTypes$1.oneOfType([PropTypes$1.bool, PropTypes$1.node]), cancelButtonColor: (_a = CButton.propTypes) === null || _a === void 0 ? void 0 : _a.color, cancelButtonSize: (_b = CButton.propTypes) === null || _b === void 0 ? void 0 : _b.size, cancelButtonVariant: (_c = CButton.propTypes) === null || _c === void 0 ? void 0 : _c.variant, calendars: PropTypes$1.number, className: PropTypes$1.string, cleaner: PropTypes$1.bool, closeOnSelect: PropTypes$1.bool, confirmButton: PropTypes$1.oneOfType([PropTypes$1.bool, PropTypes$1.node]), confirmButtonColor: (_d = CButton.propTypes) === null || _d === void 0 ? void 0 : _d.color, confirmButtonSize: (_e = CButton.propTypes) === null || _e === void 0 ? void 0 : _e.size, confirmButtonVariant: (_f = CButton.propTypes) === null || _f === void 0 ? void 0 : _f.variant, id: PropTypes$1.string, indicator: PropTypes$1.oneOfType([PropTypes$1.bool, PropTypes$1.node]), inputDateFormat: PropTypes$1.func, inputDateParse: PropTypes$1.func, inputOnChangeDelay: PropTypes$1.number, inputReadOnly: PropTypes$1.bool, placeholder: PropTypes$1.oneOfType([
        PropTypes$1.string,
        PropTypes$1.arrayOf(PropTypes$1.string.isRequired),
    ]), range: PropTypes$1.bool, ranges: PropTypes$1.object, rangesButtonsColor: (_g = CButton.propTypes) === null || _g === void 0 ? void 0 : _g.color, rangesButtonsSize: (_h = CButton.propTypes) === null || _h === void 0 ? void 0 : _h.size, rangesButtonsVariant: (_j = CButton.propTypes) === null || _j === void 0 ? void 0 : _j.variant, required: PropTypes$1.bool, separator: PropTypes$1.oneOfType([PropTypes$1.bool, PropTypes$1.node]), size: PropTypes$1.oneOf(['sm', 'lg']), timepicker: PropTypes$1.bool, todayButton: PropTypes$1.oneOfType([PropTypes$1.bool, PropTypes$1.node]), todayButtonColor: (_k = CButton.propTypes) === null || _k === void 0 ? void 0 : _k.color, todayButtonSize: (_l = CButton.propTypes) === null || _l === void 0 ? void 0 : _l.size, todayButtonVariant: (_m = CButton.propTypes) === null || _m === void 0 ? void 0 : _m.variant });

var CDatePicker = React$1.forwardRef(function (_a, ref) {
    var date = _a.date, id = _a.id, onDateChange = _a.onDateChange, _b = _a.placeholder, placeholder = _b === void 0 ? 'Select date' : _b, rest = __rest$1(_a, ["date", "id", "onDateChange", "placeholder"]);
    return (React$1.createElement(CDateRangePicker, __assign$1({ calendars: 1, id: id, startDate: date, onStartDateChange: onDateChange, placeholder: placeholder, range: false, ref: ref }, rest)));
});
CDatePicker.displayName = 'CDatePicker';
CDatePicker.propTypes = __assign$1(__assign$1({}, CDateRangePicker.propTypes), { date: PropTypes$1.oneOfType([PropTypes$1.instanceOf(Date), PropTypes$1.string]), onDateChange: PropTypes$1.func });

var getPlacement = function (placement, direction, alignment, isRTL) {
    var _placement = placement;
    if (direction === 'dropup') {
        _placement = isRTL ? 'top-end' : 'top-start';
    }
    if (direction === 'dropup-center') {
        _placement = 'top';
    }
    if (direction === 'dropend') {
        _placement = isRTL ? 'left-start' : 'right-start';
    }
    if (direction === 'dropstart') {
        _placement = isRTL ? 'right-start' : 'left-start';
    }
    if (alignment === 'end') {
        _placement = isRTL ? 'bottom-start' : 'bottom-end';
    }
    return _placement;
};
var CDropdownContext = React$1.createContext({});
var CDropdown = React$1.forwardRef(function (_a, ref) {
    var _b;
    var children = _a.children, alignment = _a.alignment, _c = _a.autoClose, autoClose = _c === void 0 ? true : _c, className = _a.className, container = _a.container, dark = _a.dark, direction = _a.direction, _d = _a.offset, offset = _d === void 0 ? [0, 2] : _d, onHide = _a.onHide, onShow = _a.onShow, _e = _a.placement, placement = _e === void 0 ? 'bottom-start' : _e, _f = _a.popper, popper = _f === void 0 ? true : _f, _g = _a.portal, portal = _g === void 0 ? false : _g, _h = _a.variant, variant = _h === void 0 ? 'btn-group' : _h, _j = _a.component, component = _j === void 0 ? 'div' : _j, _k = _a.visible, visible = _k === void 0 ? false : _k, rest = __rest$1(_a, ["children", "alignment", "autoClose", "className", "container", "dark", "direction", "offset", "onHide", "onShow", "placement", "popper", "portal", "variant", "component", "visible"]);
    var dropdownRef = React$1.useRef(null);
    // eslint-disable-next-line @typescript-eslint/no-explicit-any
    var dropdownToggleRef = React$1.useRef(null);
    var dropdownMenuRef = React$1.useRef(null);
    var forkedRef = useForkedRef(ref, dropdownRef);
    var _l = React$1.useState(visible), _visible = _l[0], setVisible = _l[1];
    var _m = usePopper(), initPopper = _m.initPopper, destroyPopper = _m.destroyPopper;
    var Component = variant === 'nav-item' ? 'li' : component;
    // Disable popper if responsive aligment is set.
    if (typeof alignment === 'object') {
        popper = false;
    }
    var contextValues = {
        alignment: alignment,
        container: container,
        dark: dark,
        dropdownToggleRef: dropdownToggleRef,
        dropdownMenuRef: dropdownMenuRef,
        popper: popper,
        portal: portal,
        variant: variant,
        visible: _visible,
        setVisible: setVisible,
    };
    var popperConfig = {
        modifiers: [
            {
                name: 'offset',
                options: {
                    offset: offset,
                },
            },
        ],
        placement: getPlacement(placement, direction, alignment, isRTL(dropdownMenuRef.current)),
    };
    React$1.useEffect(function () {
        setVisible(visible);
    }, [visible]);
    React$1.useEffect(function () {
        if (_visible && dropdownToggleRef.current && dropdownMenuRef.current) {
            popper && initPopper(dropdownToggleRef.current, dropdownMenuRef.current, popperConfig);
            window.addEventListener('mouseup', handleMouseUp);
            window.addEventListener('keyup', handleKeyup);
            onShow && onShow();
        }
        return function () {
            popper && destroyPopper();
            window.removeEventListener('mouseup', handleMouseUp);
            window.removeEventListener('keyup', handleKeyup);
            onHide && onHide();
        };
    }, [_visible]);
    var handleKeyup = function (event) {
        if (autoClose === false) {
            return;
        }
        if (event.key === 'Escape') {
            setVisible(false);
        }
    };
    var handleMouseUp = function (event) {
        if (!dropdownToggleRef.current || !dropdownMenuRef.current) {
            return;
        }
        if (dropdownToggleRef.current.contains(event.target)) {
            return;
        }
        if (autoClose === true ||
            (autoClose === 'inside' && dropdownMenuRef.current.contains(event.target)) ||
            (autoClose === 'outside' && !dropdownMenuRef.current.contains(event.target))) {
            setTimeout(function () { return setVisible(false); }, 1);
            return;
        }
    };
    return (React$1.createElement(CDropdownContext.Provider, { value: contextValues }, variant === 'input-group' ? (React$1.createElement(React$1.Fragment, null, children)) : (React$1.createElement(Component, __assign$1({ className: classNames$1(variant === 'nav-item' ? 'nav-item dropdown' : variant, (_b = {
                'dropdown-center': direction === 'center',
                'dropup dropup-center': direction === 'dropup-center'
            },
            _b["".concat(direction)] = direction && direction !== 'center' && direction !== 'dropup-center',
            _b.show = _visible,
            _b), className) }, rest, { ref: forkedRef }), children))));
});
var alignmentDirection = PropTypes$1.oneOf(['start', 'end']);
CDropdown.propTypes = {
    alignment: PropTypes$1.oneOfType([
        alignmentDirection,
        PropTypes$1.shape({ xs: alignmentDirection.isRequired }),
        PropTypes$1.shape({ sm: alignmentDirection.isRequired }),
        PropTypes$1.shape({ md: alignmentDirection.isRequired }),
        PropTypes$1.shape({ lg: alignmentDirection.isRequired }),
        PropTypes$1.shape({ xl: alignmentDirection.isRequired }),
        PropTypes$1.shape({ xxl: alignmentDirection.isRequired }),
    ]),
    autoClose: PropTypes$1.oneOfType([
        PropTypes$1.bool,
        PropTypes$1.oneOf(['inside', 'outside']),
    ]),
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    component: PropTypes$1.elementType,
    dark: PropTypes$1.bool,
    direction: PropTypes$1.oneOf(['center', 'dropup', 'dropup-center', 'dropend', 'dropstart']),
    offset: PropTypes$1.any,
    onHide: PropTypes$1.func,
    onShow: PropTypes$1.func,
    placement: placementPropType,
    popper: PropTypes$1.bool,
    portal: PropTypes$1.bool,
    variant: PropTypes$1.oneOf(['btn-group', 'dropdown', 'input-group', 'nav-item']),
    visible: PropTypes$1.bool,
};
CDropdown.displayName = 'CDropdown';

var CDropdownDivider = React$1.forwardRef(function (_a, ref) {
    var className = _a.className, rest = __rest$1(_a, ["className"]);
    return React$1.createElement("hr", __assign$1({ className: classNames$1('dropdown-divider', className) }, rest, { ref: ref }));
});
CDropdownDivider.propTypes = {
    className: PropTypes$1.string,
};
CDropdownDivider.displayName = 'CDropdownDivider';

var CDropdownHeader = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, _b = _a.component, Component = _b === void 0 ? 'h6' : _b, rest = __rest$1(_a, ["children", "className", "component"]);
    return (React$1.createElement(Component, __assign$1({ className: classNames$1('dropdown-header', className) }, rest, { ref: ref }), children));
});
CDropdownHeader.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    component: PropTypes$1.elementType,
};
CDropdownHeader.displayName = 'CDropdownHeader';

var CDropdownItem = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, _b = _a.component, component = _b === void 0 ? 'a' : _b, rest = __rest$1(_a, ["children", "className", "component"]);
    return (React$1.createElement(CLink, __assign$1({ className: classNames$1('dropdown-item', className), component: component }, rest, { ref: ref }), children));
});
CDropdownItem.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    component: PropTypes$1.elementType,
};
CDropdownItem.displayName = 'CDropdownItem';

var CDropdownItemPlain = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, _b = _a.component, Component = _b === void 0 ? 'span' : _b, rest = __rest$1(_a, ["children", "className", "component"]);
    return (React$1.createElement(Component, __assign$1({ className: classNames$1('dropdown-item-text', className) }, rest, { ref: ref }), children));
});
CDropdownItemPlain.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    component: PropTypes$1.elementType,
};
CDropdownItemPlain.displayName = 'CDropdownItemPlain';

var alignmentClassNames = function (alignment) {
    var classNames = [];
    if (typeof alignment === 'object') {
        Object.keys(alignment).map(function (key) {
            classNames.push("dropdown-menu".concat(key === 'xs' ? '' : "-".concat(key), "-").concat(alignment[key]));
        });
    }
    if (typeof alignment === 'string') {
        classNames.push("dropdown-menu-".concat(alignment));
    }
    return classNames;
};
var CDropdownMenu = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, _b = _a.component, Component = _b === void 0 ? 'ul' : _b, rest = __rest$1(_a, ["children", "className", "component"]);
    var _c = React$1.useContext(CDropdownContext), alignment = _c.alignment, container = _c.container, dark = _c.dark, dropdownMenuRef = _c.dropdownMenuRef, popper = _c.popper, portal = _c.portal, visible = _c.visible;
    var forkedRef = useForkedRef(ref, dropdownMenuRef);
    return (React$1.createElement(CConditionalPortal, { container: container, portal: portal !== null && portal !== void 0 ? portal : false },
        React$1.createElement(Component, __assign$1({ className: classNames$1('dropdown-menu', {
                'dropdown-menu-dark': dark,
                show: visible,
            }, alignment && alignmentClassNames(alignment), className), ref: forkedRef, role: "menu", "aria-hidden": !visible }, (!popper && { 'data-coreui-popper': 'static' }), rest), Component === 'ul'
            ? React$1.Children.map(children, function (child, index) {
                if (React$1.isValidElement(child)) {
                    return React$1.createElement("li", { key: index }, React$1.cloneElement(child));
                }
                return;
            })
            : children)));
});
CDropdownMenu.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    component: PropTypes$1.elementType,
};
CDropdownMenu.displayName = 'CDropdownMenu';

var CDropdownToggle = function (_a) {
    var children = _a.children, _b = _a.caret, caret = _b === void 0 ? true : _b, custom = _a.custom, className = _a.className, split = _a.split, _c = _a.trigger, trigger = _c === void 0 ? 'click' : _c, rest = __rest$1(_a, ["children", "caret", "custom", "className", "split", "trigger"]);
    var _d = React$1.useContext(CDropdownContext), dropdownToggleRef = _d.dropdownToggleRef, variant = _d.variant, visible = _d.visible, setVisible = _d.setVisible;
    var triggers = __assign$1(__assign$1({}, ((trigger === 'click' || trigger.includes('click')) && {
        onClick: function (event) {
            event.preventDefault();
            setVisible(!visible);
        },
    })), ((trigger === 'focus' || trigger.includes('focus')) && {
        onFocus: function () { return setVisible(true); },
        onBlur: function () { return setVisible(false); },
    }));
    var togglerProps = __assign$1({ className: classNames$1({
            'dropdown-toggle': caret,
            'dropdown-toggle-split': split,
            'nav-link': variant === 'nav-item',
        }, className), 'aria-expanded': visible }, (!rest.disabled && __assign$1({}, triggers)));
    // We use any because Toggler can be `a` as well as `button`.
    var Toggler = function () {
        if (custom && React$1.isValidElement(children)) {
            return (React$1.createElement(React$1.Fragment, null, React$1.cloneElement(children, __assign$1(__assign$1({ 'aria-expanded': visible }, (!rest.disabled && __assign$1({}, triggers))), { ref: dropdownToggleRef }))));
        }
        if (variant === 'nav-item') {
            return (React$1.createElement("a", __assign$1({ href: "#" }, togglerProps, { ref: dropdownToggleRef }), children));
        }
        return (React$1.createElement(CButton, __assign$1({ type: "button" }, togglerProps, { tabIndex: 0 }, rest, { ref: dropdownToggleRef }),
            children,
            split && React$1.createElement("span", { className: "visually-hidden" }, "Toggle Dropdown")));
    };
    return React$1.createElement(Toggler, null);
};
CDropdownToggle.propTypes = {
    caret: PropTypes$1.bool,
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    custom: PropTypes$1.bool,
    split: PropTypes$1.bool,
    trigger: triggerPropType,
};
CDropdownToggle.displayName = 'CDropdownToggle';

var CSpinner = React$1.forwardRef(function (_a, ref) {
    var _b;
    var className = _a.className, color = _a.color, _c = _a.component, Component = _c === void 0 ? 'div' : _c, size = _a.size, _d = _a.variant, variant = _d === void 0 ? 'border' : _d, _e = _a.visuallyHiddenLabel, visuallyHiddenLabel = _e === void 0 ? 'Loading...' : _e, rest = __rest$1(_a, ["className", "color", "component", "size", "variant", "visuallyHiddenLabel"]);
    return (React$1.createElement(Component, __assign$1({ className: classNames$1("spinner-".concat(variant), (_b = {},
            _b["spinner-".concat(variant, "-").concat(size)] = size,
            _b["text-".concat(color)] = color,
            _b), className), role: "status" }, rest, { ref: ref }),
        React$1.createElement("span", { className: "visually-hidden" }, visuallyHiddenLabel)));
});
CSpinner.propTypes = {
    className: PropTypes$1.string,
    color: colorPropType,
    component: PropTypes$1.string,
    size: PropTypes$1.oneOf(['sm']),
    variant: PropTypes$1.oneOf(['border', 'grow']),
    visuallyHiddenLabel: PropTypes$1.string,
};
CSpinner.displayName = 'CSpinner';

var CElementCover = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, boundaries = _a.boundaries, _b = _a.opacity, opacity = _b === void 0 ? 0.4 : _b, rest = __rest$1(_a, ["children", "className", "boundaries", "opacity"]);
    var elementCoverRef = React$1.useRef(null);
    var forkedRef = useForkedRef(ref, elementCoverRef);
    var _c = React$1.useState({}), customBoundaries = _c[0], setCustomBoundaries = _c[1];
    var getCustomBoundaries = function () {
        if (!elementCoverRef || !elementCoverRef.current || !boundaries) {
            return {};
        }
        var parent = elementCoverRef.current.parentElement;
        if (!parent) {
            return {};
        }
        var parentCoords = parent.getBoundingClientRect();
        var customBoundaries = {};
        boundaries.forEach(function (_a) {
            var sides = _a.sides, query = _a.query;
            var element = parent.querySelector(query);
            if (!element || !sides) {
                return;
            }
            var coords = element.getBoundingClientRect();
            sides.forEach(function (side) {
                var sideMargin = Math.abs(coords[side] - parentCoords[side]);
                customBoundaries[side] = "".concat(sideMargin, "px");
            });
        });
        return customBoundaries;
    };
    React$1.useEffect(function () {
        setCustomBoundaries(getCustomBoundaries());
    }, [JSON.stringify(getCustomBoundaries())]);
    var classes = classNames$1(className);
    var containerCoords = __assign$1({ top: 0, left: 0, right: 0, bottom: 0 }, customBoundaries);
    var coverStyles = __assign$1(__assign$1({}, containerCoords), { position: 'absolute', zIndex: 2, backgroundColor: "rgba(255,255,255,".concat(opacity, ")") });
    return (React$1.createElement("div", __assign$1({ className: classes, style: coverStyles }, rest, { ref: forkedRef }),
        React$1.createElement("div", { style: {
                position: 'absolute',
                top: '50%',
                left: '50%',
                transform: 'translateX(-50%) translateY(-50%)',
            } }, children || React$1.createElement(CSpinner, { variant: "grow", color: "primary" }))));
});
CElementCover.propTypes = {
    boundaries: PropTypes$1.array,
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    opacity: PropTypes$1.number,
};
CElementCover.displayName = 'CElementCover';

var CFooter = React$1.forwardRef(function (_a, ref) {
    var _b;
    var children = _a.children, className = _a.className, position = _a.position, rest = __rest$1(_a, ["children", "className", "position"]);
    return (React$1.createElement("div", __assign$1({ className: classNames$1('footer', (_b = {}, _b["footer-".concat(position)] = position, _b), className) }, rest, { ref: ref }), children));
});
CFooter.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    position: PropTypes$1.oneOf(['fixed', 'sticky']),
};
CFooter.displayName = 'CFooter';

var CForm = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, validated = _a.validated, rest = __rest$1(_a, ["children", "className", "validated"]);
    return (React$1.createElement("form", __assign$1({ className: classNames$1({ 'was-validated': validated }, className) || undefined }, rest, { ref: ref }), children));
});
CForm.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    validated: PropTypes$1.bool,
};
CForm.displayName = 'CForm';

var CFormCheck = React$1.forwardRef(function (_a, ref) {
    var className = _a.className, button = _a.button, feedback = _a.feedback, feedbackInvalid = _a.feedbackInvalid, feedbackValid = _a.feedbackValid, floatingLabel = _a.floatingLabel, tooltipFeedback = _a.tooltipFeedback, hitArea = _a.hitArea, id = _a.id, indeterminate = _a.indeterminate, inline = _a.inline, invalid = _a.invalid, label = _a.label, reverse = _a.reverse, _b = _a.type, type = _b === void 0 ? 'checkbox' : _b, valid = _a.valid, rest = __rest$1(_a, ["className", "button", "feedback", "feedbackInvalid", "feedbackValid", "floatingLabel", "tooltipFeedback", "hitArea", "id", "indeterminate", "inline", "invalid", "label", "reverse", "type", "valid"]);
    var inputRef = React$1.useRef(null);
    var forkedRef = useForkedRef(ref, inputRef);
    React$1.useEffect(function () {
        if (inputRef.current && indeterminate) {
            inputRef.current.indeterminate = indeterminate;
        }
    }, [indeterminate, inputRef.current]);
    var FormControl = function () { return (React$1.createElement("input", __assign$1({ type: type, className: classNames$1(button ? 'btn-check' : 'form-check-input', {
            'is-invalid': invalid,
            'is-valid': valid,
            'me-2': hitArea,
        }), id: id }, rest, { ref: forkedRef }))); };
    var FormValidation = function () { return (React$1.createElement(CFormControlValidation, { describedby: rest['aria-describedby'], feedback: feedback, feedbackInvalid: feedbackInvalid, feedbackValid: feedbackValid, floatingLabel: floatingLabel, invalid: invalid, tooltipFeedback: tooltipFeedback, valid: valid })); };
    var FormLabel = function () {
        var _a;
        return (React$1.createElement(CFormLabel, __assign$1({ customClassName: classNames$1(button
                ? classNames$1('btn', button.variant ? "btn-".concat(button.variant, "-").concat(button.color) : "btn-".concat(button.color), (_a = {},
                    _a["btn-".concat(button.size)] = button.size,
                    _a), "".concat(button.shape))
                : 'form-check-label') }, (id && { htmlFor: id })), label));
    };
    var FormCheck = function () {
        if (button) {
            return (React$1.createElement(React$1.Fragment, null,
                React$1.createElement(FormControl, null),
                label && React$1.createElement(FormLabel, null),
                React$1.createElement(FormValidation, null)));
        }
        if (label) {
            return hitArea ? (React$1.createElement(React$1.Fragment, null,
                React$1.createElement(FormControl, null),
                React$1.createElement(CFormLabel, __assign$1({ customClassName: classNames$1('form-check-label stretched-link', className) }, (id && { htmlFor: id })), label),
                React$1.createElement(FormValidation, null))) : (React$1.createElement("div", { className: classNames$1('form-check', {
                    'form-check-inline': inline,
                    'form-check-reverse': reverse,
                    'is-invalid': invalid,
                    'is-valid': valid,
                }, className) },
                React$1.createElement(FormControl, null),
                React$1.createElement(FormLabel, null),
                React$1.createElement(FormValidation, null)));
        }
        return React$1.createElement(FormControl, null);
    };
    return React$1.createElement(FormCheck, null);
});
CFormCheck.propTypes = __assign$1({ button: PropTypes$1.object, className: PropTypes$1.string, hitArea: PropTypes$1.oneOf(['full']), id: PropTypes$1.string, indeterminate: PropTypes$1.bool, inline: PropTypes$1.bool, label: PropTypes$1.oneOfType([PropTypes$1.string, PropTypes$1.node]), reverse: PropTypes$1.bool, type: PropTypes$1.oneOf(['checkbox', 'radio']) }, CFormControlValidation.propTypes);
CFormCheck.displayName = 'CFormCheck';

var CFormInput = React$1.forwardRef(function (_a, ref) {
    var _b;
    var children = _a.children, className = _a.className, _c = _a.delay, delay = _c === void 0 ? false : _c, feedback = _a.feedback, feedbackInvalid = _a.feedbackInvalid, feedbackValid = _a.feedbackValid, floatingClassName = _a.floatingClassName, floatingLabel = _a.floatingLabel, id = _a.id, invalid = _a.invalid, label = _a.label, onChange = _a.onChange, plainText = _a.plainText, size = _a.size, text = _a.text, tooltipFeedback = _a.tooltipFeedback, _d = _a.type, type = _d === void 0 ? 'text' : _d, valid = _a.valid, rest = __rest$1(_a, ["children", "className", "delay", "feedback", "feedbackInvalid", "feedbackValid", "floatingClassName", "floatingLabel", "id", "invalid", "label", "onChange", "plainText", "size", "text", "tooltipFeedback", "type", "valid"]);
    var _e = React$1.useState(), value = _e[0], setValue = _e[1];
    React$1.useEffect(function () {
        var timeOutId = setTimeout(function () { return value && onChange && onChange(value); }, typeof delay === 'number' ? delay : 500);
        return function () { return clearTimeout(timeOutId); };
    }, [value]);
    return (React$1.createElement(CFormControlWrapper, { describedby: rest['aria-describedby'], feedback: feedback, feedbackInvalid: feedbackInvalid, feedbackValid: feedbackValid, floatingClassName: floatingClassName, floatingLabel: floatingLabel, id: id, invalid: invalid, label: label, text: text, tooltipFeedback: tooltipFeedback, valid: valid },
        React$1.createElement("input", __assign$1({ className: classNames$1(plainText ? 'form-control-plaintext' : 'form-control', (_b = {},
                _b["form-control-".concat(size)] = size,
                _b['form-control-color'] = type === 'color',
                _b['is-invalid'] = invalid,
                _b['is-valid'] = valid,
                _b), className), id: id, type: type, onChange: function (event) { return (delay ? setValue(event) : onChange && onChange(event)); } }, rest, { ref: ref }), children)));
});
CFormInput.propTypes = __assign$1({ className: PropTypes$1.string, id: PropTypes$1.string, delay: PropTypes$1.oneOfType([PropTypes$1.bool, PropTypes$1.number]), plainText: PropTypes$1.bool, size: PropTypes$1.oneOf(['sm', 'lg']), type: PropTypes$1.oneOfType([PropTypes$1.oneOf(['color', 'file', 'text']), PropTypes$1.string]) }, CFormControlWrapper.propTypes);
CFormInput.displayName = 'CFormInput';

var CFormRange = React$1.forwardRef(function (_a, ref) {
    var className = _a.className, label = _a.label, rest = __rest$1(_a, ["className", "label"]);
    return (React$1.createElement(React$1.Fragment, null,
        label && React$1.createElement(CFormLabel, { htmlFor: rest.id }, label),
        React$1.createElement("input", __assign$1({ type: "range", className: classNames$1('form-range', className) }, rest, { ref: ref }))));
});
CFormRange.propTypes = {
    className: PropTypes$1.string,
    label: PropTypes$1.oneOfType([PropTypes$1.node, PropTypes$1.string]),
};
CFormRange.displayName = 'CFormRange';

var CFormSelect = React$1.forwardRef(function (_a, ref) {
    var _b;
    var children = _a.children, className = _a.className, feedback = _a.feedback, feedbackInvalid = _a.feedbackInvalid, feedbackValid = _a.feedbackValid, floatingClassName = _a.floatingClassName, floatingLabel = _a.floatingLabel, htmlSize = _a.htmlSize, id = _a.id, invalid = _a.invalid, label = _a.label, options = _a.options, size = _a.size, text = _a.text, tooltipFeedback = _a.tooltipFeedback, valid = _a.valid, rest = __rest$1(_a, ["children", "className", "feedback", "feedbackInvalid", "feedbackValid", "floatingClassName", "floatingLabel", "htmlSize", "id", "invalid", "label", "options", "size", "text", "tooltipFeedback", "valid"]);
    return (React$1.createElement(CFormControlWrapper, { describedby: rest['aria-describedby'], feedback: feedback, feedbackInvalid: feedbackInvalid, feedbackValid: feedbackValid, floatingClassName: floatingClassName, floatingLabel: floatingLabel, id: id, invalid: invalid, label: label, text: text, tooltipFeedback: tooltipFeedback, valid: valid },
        React$1.createElement("select", __assign$1({ id: id, className: classNames$1('form-select', (_b = {},
                _b["form-select-".concat(size)] = size,
                _b['is-invalid'] = invalid,
                _b['is-valid'] = valid,
                _b), className), size: htmlSize }, rest, { ref: ref }), options
            ? options.map(function (option, index) {
                return (React$1.createElement("option", __assign$1({}, (typeof option === 'object' &&
                    option.disabled && { disabled: option.disabled }), (typeof option === 'object' &&
                    option.value !== undefined && { value: option.value }), { key: index }), typeof option === 'string' ? option : option.label));
            })
            : children)));
});
CFormSelect.propTypes = __assign$1({ className: PropTypes$1.string, htmlSize: PropTypes$1.number, options: PropTypes$1.array }, CFormControlWrapper.propTypes);
CFormSelect.displayName = 'CFormSelect';

var CFormSwitch = React$1.forwardRef(function (_a, ref) {
    var _b;
    var className = _a.className, id = _a.id, invalid = _a.invalid, label = _a.label, reverse = _a.reverse, size = _a.size, _c = _a.type, type = _c === void 0 ? 'checkbox' : _c, valid = _a.valid, rest = __rest$1(_a, ["className", "id", "invalid", "label", "reverse", "size", "type", "valid"]);
    return (React$1.createElement("div", { className: classNames$1('form-check form-switch', (_b = {
                'form-check-reverse': reverse
            },
            _b["form-switch-".concat(size)] = size,
            _b['is-invalid'] = invalid,
            _b['is-valid'] = valid,
            _b), className) },
        React$1.createElement("input", __assign$1({ type: type, className: classNames$1('form-check-input', {
                'is-invalid': invalid,
                'is-valid': valid,
            }), id: id }, rest, { ref: ref })),
        label && (React$1.createElement(CFormLabel, __assign$1({ customClassName: "form-check-label" }, (id && { htmlFor: id })), label))));
});
CFormSwitch.propTypes = {
    className: PropTypes$1.string,
    id: PropTypes$1.string,
    invalid: PropTypes$1.bool,
    label: PropTypes$1.oneOfType([PropTypes$1.string, PropTypes$1.node]),
    reverse: PropTypes$1.bool,
    size: PropTypes$1.oneOf(['lg', 'xl']),
    type: PropTypes$1.oneOf(['checkbox', 'radio']),
    valid: PropTypes$1.bool,
};
CFormSwitch.displayName = 'CFormSwitch';

var CFormTextarea = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, feedback = _a.feedback, feedbackInvalid = _a.feedbackInvalid, feedbackValid = _a.feedbackValid, floatingClassName = _a.floatingClassName, floatingLabel = _a.floatingLabel, id = _a.id, invalid = _a.invalid, label = _a.label, plainText = _a.plainText, text = _a.text, tooltipFeedback = _a.tooltipFeedback, valid = _a.valid, rest = __rest$1(_a, ["children", "className", "feedback", "feedbackInvalid", "feedbackValid", "floatingClassName", "floatingLabel", "id", "invalid", "label", "plainText", "text", "tooltipFeedback", "valid"]);
    return (React$1.createElement(CFormControlWrapper, { describedby: rest['aria-describedby'], feedback: feedback, feedbackInvalid: feedbackInvalid, feedbackValid: feedbackValid, floatingClassName: floatingClassName, floatingLabel: floatingLabel, id: id, invalid: invalid, label: label, text: text, tooltipFeedback: tooltipFeedback, valid: valid },
        React$1.createElement("textarea", __assign$1({ className: classNames$1(plainText ? 'form-control-plaintext' : 'form-control', {
                'is-invalid': invalid,
                'is-valid': valid,
            }, className), id: id }, rest, { ref: ref }), children)));
});
CFormTextarea.propTypes = __assign$1({ className: PropTypes$1.string, id: PropTypes$1.string, plainText: PropTypes$1.bool }, CFormControlWrapper.propTypes);
CFormTextarea.displayName = 'CFormTextarea';

var CInputGroup = React$1.forwardRef(function (_a, ref) {
    var _b;
    var children = _a.children, className = _a.className, size = _a.size, rest = __rest$1(_a, ["children", "className", "size"]);
    return (React$1.createElement("div", __assign$1({ className: classNames$1('input-group', (_b = {},
            _b["input-group-".concat(size)] = size,
            _b), className) }, rest, { ref: ref }), children));
});
CInputGroup.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    size: PropTypes$1.oneOf(['sm', 'lg']),
};
CInputGroup.displayName = 'CInputGroup';

var CInputGroupText = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, _b = _a.component, Component = _b === void 0 ? 'span' : _b, rest = __rest$1(_a, ["children", "className", "component"]);
    return (React$1.createElement(Component, __assign$1({ className: classNames$1('input-group-text', className) }, rest, { ref: ref }), children));
});
CInputGroupText.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    component: PropTypes$1.elementType,
};
CInputGroupText.displayName = 'CInputGroupText';

var BREAKPOINTS$3 = [
    'xxl',
    'xl',
    'lg',
    'md',
    'sm',
    'xs',
];
var CCol = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, rest = __rest$1(_a, ["children", "className"]);
    var repsonsiveClassNames = [];
    BREAKPOINTS$3.forEach(function (bp) {
        var breakpoint = rest[bp];
        delete rest[bp];
        var infix = bp === 'xs' ? '' : "-".concat(bp);
        if (typeof breakpoint === 'number' || typeof breakpoint === 'string') {
            repsonsiveClassNames.push("col".concat(infix, "-").concat(breakpoint));
        }
        if (typeof breakpoint === 'boolean') {
            repsonsiveClassNames.push("col".concat(infix));
        }
        if (breakpoint && typeof breakpoint === 'object') {
            if (typeof breakpoint.span === 'number' || typeof breakpoint.span === 'string') {
                repsonsiveClassNames.push("col".concat(infix, "-").concat(breakpoint.span));
            }
            if (typeof breakpoint.span === 'boolean') {
                repsonsiveClassNames.push("col".concat(infix));
            }
            if (typeof breakpoint.order === 'number' || typeof breakpoint.order === 'string') {
                repsonsiveClassNames.push("order".concat(infix, "-").concat(breakpoint.order));
            }
            if (typeof breakpoint.offset === 'number') {
                repsonsiveClassNames.push("offset".concat(infix, "-").concat(breakpoint.offset));
            }
        }
    });
    return (React$1.createElement("div", __assign$1({ className: classNames$1(repsonsiveClassNames.length > 0 ? repsonsiveClassNames : 'col', className) }, rest, { ref: ref }), children));
});
var span = PropTypes$1.oneOfType([
    PropTypes$1.bool,
    PropTypes$1.number,
    PropTypes$1.string,
    PropTypes$1.oneOf(['auto']),
]);
var col = PropTypes$1.oneOfType([
    span,
    PropTypes$1.shape({
        span: span,
        offset: PropTypes$1.oneOfType([PropTypes$1.number, PropTypes$1.string]),
        order: PropTypes$1.oneOfType([
            PropTypes$1.oneOf(['first', 'last']),
            PropTypes$1.number,
            PropTypes$1.string,
        ]),
    }),
]);
CCol.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    xs: col,
    sm: col,
    md: col,
    lg: col,
    xl: col,
    xxl: col,
};
CCol.displayName = 'CCol';

var BREAKPOINTS$2 = [
    'xxl',
    'xl',
    'lg',
    'md',
    'sm',
    'fluid',
];
var CContainer = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, rest = __rest$1(_a, ["children", "className"]);
    var repsonsiveClassNames = [];
    BREAKPOINTS$2.forEach(function (bp) {
        var breakpoint = rest[bp];
        delete rest[bp];
        breakpoint && repsonsiveClassNames.push("container-".concat(bp));
    });
    return (React$1.createElement("div", __assign$1({ className: classNames$1(repsonsiveClassNames.length > 0 ? repsonsiveClassNames : 'container', className) }, rest, { ref: ref }), children));
});
CContainer.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    sm: PropTypes$1.bool,
    md: PropTypes$1.bool,
    lg: PropTypes$1.bool,
    xl: PropTypes$1.bool,
    xxl: PropTypes$1.bool,
    fluid: PropTypes$1.bool,
};
CContainer.displayName = 'CContainer';

var BREAKPOINTS$1 = [
    'xxl',
    'xl',
    'lg',
    'md',
    'sm',
    'xs',
];
var CRow = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, rest = __rest$1(_a, ["children", "className"]);
    var repsonsiveClassNames = [];
    BREAKPOINTS$1.forEach(function (bp) {
        var breakpoint = rest[bp];
        delete rest[bp];
        var infix = bp === 'xs' ? '' : "-".concat(bp);
        if (typeof breakpoint === 'object') {
            if (breakpoint.cols) {
                repsonsiveClassNames.push("row-cols".concat(infix, "-").concat(breakpoint.cols));
            }
            if (typeof breakpoint.gutter === 'number') {
                repsonsiveClassNames.push("g".concat(infix, "-").concat(breakpoint.gutter));
            }
            if (typeof breakpoint.gutterX === 'number') {
                repsonsiveClassNames.push("gx".concat(infix, "-").concat(breakpoint.gutterX));
            }
            if (typeof breakpoint.gutterY === 'number') {
                repsonsiveClassNames.push("gy".concat(infix, "-").concat(breakpoint.gutterY));
            }
        }
    });
    return (React$1.createElement("div", { className: classNames$1('row', repsonsiveClassNames, className), ref: ref }, children));
});
var bp = PropTypes$1.shape({
    cols: PropTypes$1.oneOfType([PropTypes$1.oneOf(['auto']), PropTypes$1.number, PropTypes$1.string]),
    gutter: PropTypes$1.oneOfType([PropTypes$1.string, PropTypes$1.number]),
    gutterX: PropTypes$1.oneOfType([PropTypes$1.string, PropTypes$1.number]),
    gutterY: PropTypes$1.oneOfType([PropTypes$1.string, PropTypes$1.number]),
});
CRow.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    xs: bp,
    sm: bp,
    md: bp,
    lg: bp,
    xl: bp,
    xxl: bp,
};
CRow.displayName = 'CRow';

var CHeader = React$1.forwardRef(function (_a, ref) {
    var _b;
    var children = _a.children, className = _a.className, container = _a.container, position = _a.position, rest = __rest$1(_a, ["children", "className", "container", "position"]);
    return (React$1.createElement("div", __assign$1({ className: classNames$1('header', (_b = {}, _b["header-".concat(position)] = position, _b), className) }, rest, { ref: ref }), container ? (React$1.createElement("div", { className: typeof container === 'string' ? "container-".concat(container) : 'container' }, children)) : (React$1.createElement(React$1.Fragment, null, children))));
});
CHeader.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    container: PropTypes$1.oneOfType([
        PropTypes$1.bool,
        PropTypes$1.oneOf([
            'sm',
            'md',
            'lg',
            'xl',
            'xxl',
            'fluid',
        ]),
    ]),
    position: PropTypes$1.oneOf(['fixed', 'sticky']),
};
CHeader.displayName = 'CHeader';

var CHeaderBrand = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, _b = _a.component, Component = _b === void 0 ? 'a' : _b, className = _a.className, rest = __rest$1(_a, ["children", "component", "className"]);
    return (React$1.createElement(Component, __assign$1({ className: classNames$1('header-brand', className) }, rest, { ref: ref }), children));
});
CHeaderBrand.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    component: PropTypes$1.elementType,
};
CHeaderBrand.displayName = 'CHeaderBrand';

var CHeaderDivider = React$1.forwardRef(function (_a, ref) {
    var className = _a.className, rest = __rest$1(_a, ["className"]);
    return React$1.createElement("div", __assign$1({ className: classNames$1('header-divider', className) }, rest, { ref: ref }));
});
CHeaderDivider.propTypes = {
    className: PropTypes$1.string,
};
CHeaderDivider.displayName = 'CHeaderDivider';

var CHeaderNav = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, _b = _a.component, Component = _b === void 0 ? 'ul' : _b, className = _a.className, rest = __rest$1(_a, ["children", "component", "className"]);
    return (React$1.createElement(Component, __assign$1({ className: classNames$1('header-nav', className), role: "navigation" }, rest, { ref: ref }), children));
});
CHeaderNav.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    component: PropTypes$1.elementType,
};
CHeaderNav.displayName = 'CHeaderNav';

var CHeaderText = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, rest = __rest$1(_a, ["children", "className"]);
    return (React$1.createElement("span", __assign$1({ className: classNames$1('header-text', className) }, rest, { ref: ref }), children));
});
CHeaderText.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
};
CHeaderText.displayName = 'CHeaderText';

var CHeaderToggler = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, rest = __rest$1(_a, ["children", "className"]);
    return (React$1.createElement("button", __assign$1({ type: "button", className: classNames$1('header-toggler', className) }, rest, { ref: ref }), children !== null && children !== void 0 ? children : React$1.createElement("span", { className: "header-toggler-icon" })));
});
CHeaderToggler.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
};
CHeaderToggler.displayName = 'CHeaderToggler';

var CImage = React$1.forwardRef(function (_a, ref) {
    var _b;
    var align = _a.align, className = _a.className, fluid = _a.fluid, rounded = _a.rounded, thumbnail = _a.thumbnail, rest = __rest$1(_a, ["align", "className", "fluid", "rounded", "thumbnail"]);
    return (React$1.createElement("img", __assign$1({ className: classNames$1((_b = {},
            _b["float-".concat(align)] = align && (align === 'start' || align === 'end'),
            _b['d-block mx-auto'] = align && align === 'center',
            _b['img-fluid'] = fluid,
            _b.rounded = rounded,
            _b['img-thumbnail'] = thumbnail,
            _b), className) || undefined }, rest, { ref: ref })));
});
CImage.propTypes = {
    align: PropTypes$1.oneOf(['start', 'center', 'end']),
    className: PropTypes$1.string,
    fluid: PropTypes$1.bool,
    rounded: PropTypes$1.bool,
    thumbnail: PropTypes$1.bool,
};
CImage.displayName = 'CImage';

var CListGroup = React$1.forwardRef(function (_a, ref) {
    var _b;
    var children = _a.children, className = _a.className, _c = _a.component, Component = _c === void 0 ? 'ul' : _c, flush = _a.flush, layout = _a.layout;
    return (React$1.createElement(Component, { className: classNames$1('list-group', (_b = {
                'list-group-flush': flush
            },
            _b["list-group-".concat(layout)] = layout,
            _b), className), ref: ref }, children));
});
CListGroup.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    component: PropTypes$1.elementType,
    flush: PropTypes$1.bool,
    layout: PropTypes$1.oneOf([
        'horizontal',
        'horizontal-sm',
        'horizontal-md',
        'horizontal-lg',
        'horizontal-xl',
        'horizontal-xxl',
    ]),
};
CListGroup.displayName = 'CListGroup';

var CListGroupItem = React$1.forwardRef(function (_a, ref) {
    var _b;
    var children = _a.children, active = _a.active, className = _a.className, disabled = _a.disabled, color = _a.color, _c = _a.component, component = _c === void 0 ? 'li' : _c, rest = __rest$1(_a, ["children", "active", "className", "disabled", "color", "component"]);
    var Component = component === 'a' || component === 'button' ? CLink : component;
    rest = __assign$1(__assign$1(__assign$1(__assign$1({}, ((component === 'a' || component === 'button') && {
        active: active,
        disabled: disabled,
        component: component,
        ref: ref,
    })), (active && { 'aria-current': true })), (disabled && { 'aria-disabled': true })), rest);
    return (React$1.createElement(Component, __assign$1({ className: classNames$1('list-group-item', (_b = {},
            _b["list-group-item-".concat(color)] = color,
            _b['list-group-item-action'] = component === 'a' || component === 'button',
            _b.active = active,
            _b.disabled = disabled,
            _b), className) }, rest), children));
});
CListGroupItem.propTypes = {
    active: PropTypes$1.bool,
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    color: colorPropType,
    component: PropTypes$1.elementType,
    disabled: PropTypes$1.bool,
};
CListGroupItem.displayName = 'CListGroupItem';

var CLoadingButton = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, disabledOnLoading = _a.disabledOnLoading, loading = _a.loading, onClick = _a.onClick, _b = _a.spinnerType, spinnerType = _b === void 0 ? 'border' : _b, timeout = _a.timeout, rest = __rest$1(_a, ["children", "className", "disabledOnLoading", "loading", "onClick", "spinnerType", "timeout"]);
    var _c = React$1.useState(), _loading = _c[0], setLoading = _c[1];
    React$1.useEffect(function () {
        setLoading(loading);
    }, [loading]);
    var handleOnClick = function () {
        onClick && onClick();
        if (timeout) {
            setLoading(true);
            setTimeout(function () {
                setLoading(false);
            }, timeout);
        }
    };
    return (React$1.createElement(CButton, __assign$1({ className: classNames$1('btn-loading', _loading && 'is-loading', className) }, (disabledOnLoading && _loading && { disabled: true }), { onClick: handleOnClick }, rest, { ref: ref }),
        React$1.createElement(CSpinner, { className: "btn-loading-spinner", size: "sm", variant: spinnerType }),
        children));
});
CLoadingButton.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    disabledOnLoading: PropTypes$1.bool,
    loading: PropTypes$1.bool,
    onClick: PropTypes$1.func,
    spinnerType: PropTypes$1.oneOf(['border', 'grow']),
    timeout: PropTypes$1.number,
};
CLoadingButton.displayName = 'CLoadingButton';

var CModalContent = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, rest = __rest$1(_a, ["children", "className"]);
    return (React$1.createElement("div", __assign$1({ className: classNames$1('modal-content', className) }, rest, { ref: ref }), children));
});
CModalContent.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
};
CModalContent.displayName = 'CModalContent';

var CModalDialog = React$1.forwardRef(function (_a, ref) {
    var _b;
    var children = _a.children, alignment = _a.alignment, className = _a.className, fullscreen = _a.fullscreen, scrollable = _a.scrollable, size = _a.size, rest = __rest$1(_a, ["children", "alignment", "className", "fullscreen", "scrollable", "size"]);
    return (React$1.createElement("div", __assign$1({ className: classNames$1('modal-dialog', (_b = {
                'modal-dialog-centered': alignment === 'center'
            },
            _b[typeof fullscreen === 'boolean'
                ? 'modal-fullscreen'
                : "modal-fullscreen-".concat(fullscreen, "-down")] = fullscreen,
            _b['modal-dialog-scrollable'] = scrollable,
            _b["modal-".concat(size)] = size,
            _b), className) }, rest, { ref: ref }), children));
});
CModalDialog.propTypes = {
    alignment: PropTypes$1.oneOf(['top', 'center']),
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    fullscreen: PropTypes$1.oneOfType([
        PropTypes$1.bool,
        PropTypes$1.oneOf(['sm', 'md', 'lg', 'xl', 'xxl']),
    ]),
    scrollable: PropTypes$1.bool,
    size: PropTypes$1.oneOf(['sm', 'lg', 'xl']),
};
CModalDialog.displayName = 'CModalDialog';

var CModalContext = React$1.createContext({});
var CModal = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, alignment = _a.alignment, _b = _a.backdrop, backdrop = _b === void 0 ? true : _b, className = _a.className, _c = _a.duration, duration = _c === void 0 ? 150 : _c, _d = _a.focus, focus = _d === void 0 ? true : _d, fullscreen = _a.fullscreen, _e = _a.keyboard, keyboard = _e === void 0 ? true : _e, onClose = _a.onClose, onClosePrevented = _a.onClosePrevented, onShow = _a.onShow, _f = _a.portal, portal = _f === void 0 ? true : _f, scrollable = _a.scrollable, size = _a.size, _g = _a.transition, transition = _g === void 0 ? true : _g, _h = _a.unmountOnClose, unmountOnClose = _h === void 0 ? true : _h, visible = _a.visible, rest = __rest$1(_a, ["children", "alignment", "backdrop", "className", "duration", "focus", "fullscreen", "keyboard", "onClose", "onClosePrevented", "onShow", "portal", "scrollable", "size", "transition", "unmountOnClose", "visible"]);
    var activeElementRef = React$1.useRef(null);
    var modalRef = React$1.useRef(null);
    var modalContentRef = React$1.useRef(null);
    var forkedRef = useForkedRef(ref, modalRef);
    var _j = React$1.useState(visible), _visible = _j[0], setVisible = _j[1];
    var _k = React$1.useState(false), staticBackdrop = _k[0], setStaticBackdrop = _k[1];
    var contextValues = {
        visible: _visible,
        setVisible: setVisible,
    };
    React$1.useEffect(function () {
        setVisible(visible);
    }, [visible]);
    React$1.useEffect(function () {
        var _a;
        if (_visible) {
            activeElementRef.current = document.activeElement;
            document.addEventListener('mouseup', handleClickOutside);
            document.addEventListener('keydown', handleKeyDown);
        }
        else {
            (_a = activeElementRef.current) === null || _a === void 0 ? void 0 : _a.focus();
        }
        return function () {
            document.removeEventListener('mouseup', handleClickOutside);
            document.removeEventListener('keydown', handleKeyDown);
        };
    }, [_visible]);
    var handleDismiss = function () {
        if (backdrop === 'static') {
            return setStaticBackdrop(true);
        }
        setVisible(false);
        return onClose && onClose();
    };
    React$1.useLayoutEffect(function () {
        onClosePrevented && onClosePrevented();
        setTimeout(function () { return setStaticBackdrop(false); }, duration);
    }, [staticBackdrop]);
    // Set focus to modal after open
    React$1.useLayoutEffect(function () {
        if (_visible) {
            document.body.classList.add('modal-open');
            if (backdrop) {
                document.body.style.overflow = 'hidden';
                document.body.style.paddingRight = '0px';
            }
            setTimeout(function () {
                var _a;
                focus && ((_a = modalRef.current) === null || _a === void 0 ? void 0 : _a.focus());
            }, transition ? duration : 0);
        }
        else {
            document.body.classList.remove('modal-open');
            if (backdrop) {
                document.body.style.removeProperty('overflow');
                document.body.style.removeProperty('padding-right');
            }
        }
        return function () {
            document.body.classList.remove('modal-open');
            if (backdrop) {
                document.body.style.removeProperty('overflow');
                document.body.style.removeProperty('padding-right');
            }
        };
    }, [_visible]);
    var handleClickOutside = function (event) {
        if (modalRef.current && modalRef.current == event.target) {
            handleDismiss();
        }
    };
    var handleKeyDown = function (event) {
        if (event.key === 'Escape' && keyboard) {
            handleDismiss();
        }
    };
    return (React$1.createElement(React$1.Fragment, null,
        React$1.createElement(Transition$1, { in: _visible, mountOnEnter: true, nodeRef: modalRef, onEnter: onShow, onExit: onClose, unmountOnExit: unmountOnClose, timeout: transition ? duration : 0 }, function (state) { return (React$1.createElement(CConditionalPortal, { portal: portal },
            React$1.createElement(CModalContext.Provider, { value: contextValues },
                React$1.createElement("div", __assign$1({ className: classNames$1('modal', {
                        'modal-static': staticBackdrop,
                        fade: transition,
                        show: state === 'entered',
                    }, className), tabIndex: -1 }, (_visible
                    ? { 'aria-modal': true, role: 'dialog' }
                    : { 'aria-hidden': 'true' }), { style: __assign$1({}, (state !== 'exited' && { display: 'block' })) }, rest, { ref: forkedRef }),
                    React$1.createElement(CModalDialog, { alignment: alignment, fullscreen: fullscreen, scrollable: scrollable, size: size },
                        React$1.createElement(CModalContent, { ref: modalContentRef }, children)))))); }),
        backdrop && (React$1.createElement(CConditionalPortal, { portal: portal },
            React$1.createElement(CBackdrop, { visible: _visible })))));
});
CModal.propTypes = {
    alignment: PropTypes$1.oneOf(['top', 'center']),
    backdrop: PropTypes$1.oneOfType([PropTypes$1.bool, PropTypes$1.oneOf(['static'])]),
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    duration: PropTypes$1.number,
    focus: PropTypes$1.bool,
    fullscreen: PropTypes$1.oneOfType([
        PropTypes$1.bool,
        PropTypes$1.oneOf(['sm', 'md', 'lg', 'xl', 'xxl']),
    ]),
    keyboard: PropTypes$1.bool,
    onClose: PropTypes$1.func,
    onClosePrevented: PropTypes$1.func,
    onShow: PropTypes$1.func,
    portal: PropTypes$1.bool,
    scrollable: PropTypes$1.bool,
    size: PropTypes$1.oneOf(['sm', 'lg', 'xl']),
    transition: PropTypes$1.bool,
    unmountOnClose: PropTypes$1.bool,
    visible: PropTypes$1.bool,
};
CModal.displayName = 'CModal';

var CModalBody = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, rest = __rest$1(_a, ["children", "className"]);
    return (React$1.createElement("div", __assign$1({ className: classNames$1('modal-body', className) }, rest, { ref: ref }), children));
});
CModalBody.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
};
CModalBody.displayName = 'CModalBody';

var CModalFooter = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, rest = __rest$1(_a, ["children", "className"]);
    return (React$1.createElement("div", __assign$1({ className: classNames$1('modal-footer', className) }, rest, { ref: ref }), children));
});
CModalFooter.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
};
CModalFooter.displayName = 'CModalFooter';

var CModalHeader = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, _b = _a.closeButton, closeButton = _b === void 0 ? true : _b, rest = __rest$1(_a, ["children", "className", "closeButton"]);
    var setVisible = React$1.useContext(CModalContext).setVisible;
    return (React$1.createElement("div", __assign$1({ className: classNames$1('modal-header', className) }, rest, { ref: ref }),
        children,
        closeButton && React$1.createElement(CCloseButton, { onClick: function () { return setVisible(false); } })));
});
CModalHeader.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    closeButton: PropTypes$1.bool,
};
CModalHeader.displayName = 'CModalHeader';

var CModalTitle = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, _b = _a.component, Component = _b === void 0 ? 'h5' : _b, className = _a.className, rest = __rest$1(_a, ["children", "component", "className"]);
    return (React$1.createElement(Component, __assign$1({ className: classNames$1('modal-title', className) }, rest, { ref: ref }), children));
});
CModalTitle.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    component: PropTypes$1.elementType,
};
CModalTitle.displayName = 'CModalTitle';

var createNativeOptions = function (options) {
    return options &&
        options.map(function (option, index) {
            return option.options ? (React$1.createElement("optgroup", { label: option.label, key: index }, createNativeOptions(option.options))) : (React$1.createElement("option", { value: option.value, key: index, disabled: option.disabled }, option.text));
        });
};
var CMultiSelectNativeSelect = React$1.forwardRef(function (_a, ref) {
    var id = _a.id, options = _a.options, rest = __rest$1(_a, ["id", "options"]);
    return (React$1.createElement("select", __assign$1({ className: "multi-select-new" }, (id && { id: "".concat(id, "-multi-select") }), (id && { name: "".concat(id, "-multi-select") }), { tabIndex: -1, style: { display: 'none' } }, rest, { ref: ref }), options && createNativeOptions(options)));
});
CMultiSelectNativeSelect.propTypes = {
    options: PropTypes$1.array,
    value: PropTypes$1.oneOfType([
        PropTypes$1.number,
        PropTypes$1.string,
        PropTypes$1.arrayOf(PropTypes$1.string.isRequired),
    ]),
};
CMultiSelectNativeSelect.displayName = 'CMultiSelectNativeSelect';

var CVirtualScroller = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, visibleItems = _a.visibleItems, onScroll = _a.onScroll;
    var virtualScrollRef = React$1.useRef(null);
    var virtualScrollContentRef = React$1.useRef(null);
    var forkedRef = useForkedRef(ref, virtualScrollRef);
    var _b = React$1.useState(Math.floor(visibleItems / 2)), buffer = _b[0], setBuffer = _b[1];
    var _c = React$1.useState(1), currentItemIndex = _c[0], setCurrentItemIndex = _c[1];
    var _d = React$1.useState(0), itemHeight = _d[0], setItemHeight = _d[1];
    var _e = React$1.useState(React$1.Children.count(children)), itemsNumber = _e[0], setItemsNumber = _e[1];
    var _f = React$1.useState(0), viewportPadding = _f[0], setViewportPadding = _f[1];
    var _g = React$1.useState(visibleItems * itemHeight + 2 * viewportPadding), viewportHeight = _g[0], setViewportHeight = _g[1];
    var _h = React$1.useState(itemsNumber * itemHeight + 2 * viewportPadding), maxHeight = _h[0], setMaxHeight = _h[1];
    React$1.useEffect(function () {
        virtualScrollRef.current && virtualScrollRef.current.scrollTop;
        virtualScrollRef.current &&
            setViewportPadding(Number.parseFloat(getComputedStyle(virtualScrollRef.current).paddingTop));
    });
    React$1.useEffect(function () {
        setItemsNumber(React$1.Children.count(children));
    }, [children]);
    React$1.useEffect(function () {
        setViewportHeight(Math.min(visibleItems, itemsNumber) * itemHeight + 2 * viewportPadding);
    }, [itemHeight, itemsNumber, viewportPadding, visibleItems]);
    React$1.useEffect(function () {
        setMaxHeight(itemsNumber * itemHeight);
        virtualScrollRef.current && virtualScrollRef.current.scrollTop;
    }, [itemHeight, itemsNumber]);
    React$1.useEffect(function () {
        setBuffer(Math.floor(visibleItems / 2));
    }, [visibleItems]);
    var handleScroll = function (scrollTop) {
        var _currentItemIndex = itemHeight && Math.max(Math.ceil(scrollTop / itemHeight), 1);
        setCurrentItemIndex(_currentItemIndex);
        onScroll && onScroll(_currentItemIndex);
    };
    return (React$1.createElement("div", { className: classNames$1('virtual-scroller', className), onScroll: function (event) {
            return handleScroll(event.target.scrollTop);
        }, ref: forkedRef, style: {
            height: viewportHeight,
            overflowY: 'auto',
        } },
        React$1.createElement("div", { className: "virtual-scroller-content", style: {
                height: maxHeight,
            }, ref: virtualScrollContentRef }, React$1.Children.map(children, function (child, index) {
            if (React$1.isValidElement(child) &&
                index + 1 > Math.max(currentItemIndex - buffer, 0) &&
                index + 1 <= currentItemIndex + visibleItems + buffer) {
                return React$1.cloneElement(child, {
                    className: classNames$1(child.props.className, {
                        'virtual-scroller-item-preload': index + 1 > currentItemIndex + visibleItems || index + 1 < currentItemIndex,
                    }),
                    key: index,
                    style: __assign$1({}, (currentItemIndex > buffer && {
                        transform: "translateY(".concat((currentItemIndex - buffer) * itemHeight, "px)"),
                    })),
                    ref: function (node) {
                        return node &&
                            node.offsetHeight &&
                            setItemHeight(node.offsetHeight +
                                Number.parseFloat(getComputedStyle(node).marginTop) +
                                Number.parseFloat(getComputedStyle(node).marginBottom));
                    },
                });
            }
            return;
        }))));
});
CVirtualScroller.propTypes = {
    onScroll: PropTypes$1.func,
    visibleItems: PropTypes$1.number.isRequired,
};
CVirtualScroller.displayName = 'CVirtualScroller';

var createOption = function (text, options) {
    var value = text.toLowerCase().replace(/\s/g, '-');
    var uniqueValue = value;
    var i = 1;
    while (options.some(function (option) { return String(option.value) === uniqueValue; })) {
        uniqueValue = "".concat(value, "-").concat(i);
        i++;
    }
    return [
        {
            value: uniqueValue,
            text: text,
            custom: true,
        },
    ];
};
var filterOptionsList = function (search, _options) {
    if (search.length > 0 && _options) {
        var optionsList = [];
        for (var _i = 0, _options_1 = _options; _i < _options_1.length; _i++) {
            var option = _options_1[_i];
            var options = option.options &&
                option.options.filter(function (option) {
                    return option.text && option.text.toLowerCase().includes(search.toLowerCase());
                });
            if ((option.text && option.text.toLowerCase().includes(search.toLowerCase())) ||
                (options && options.length > 0)) {
                optionsList.push(Object.assign({}, option, options && options.length > 0 && { options: options }));
            }
        }
        return optionsList;
    }
    return _options;
};
var flattenOptionsArray = function (options, keepGroupLabel) {
    var optionsList = [];
    for (var _i = 0, options_1 = options; _i < options_1.length; _i++) {
        var option = options_1[_i];
        if (Array.isArray(option.options)) {
            var options_2 = option.options, rest = __rest$1(option, ["options"]);
            if (keepGroupLabel) {
                optionsList.push(rest);
            }
            optionsList.push.apply(optionsList, options_2);
        }
        else {
            optionsList.push(option);
        }
    }
    return optionsList;
};
var getNextSibling = function (elem, selector) {
    // Get the next sibling element
    var sibling = elem.nextElementSibling;
    // If there's no selector, return the first sibling
    if (!selector)
        return sibling;
    // If the sibling matches our selector, use it
    // If not, jump to the next sibling and continue the loop
    while (sibling) {
        if (sibling.matches(selector))
            return sibling;
        sibling = sibling.nextElementSibling;
    }
    return;
};
var getPreviousSibling = function (elem, selector) {
    // Get the next sibling element
    var sibling = elem.previousElementSibling;
    // If there's no selector, return the first sibling
    if (!selector)
        return sibling;
    // If the sibling matches our selector, use it
    // If not, jump to the next sibling and continue the loop
    while (sibling) {
        if (sibling.matches(selector))
            return sibling;
        sibling = sibling.previousElementSibling;
    }
    return;
};
var selectOptions = function (options, selected, deselected) {
    var _selected = __spreadArray(__spreadArray([], selected, true), options, true);
    if (deselected) {
        _selected = _selected.filter(function (selectedOption) {
            return !deselected.some(function (deselectedOption) { return deselectedOption.value === selectedOption.value; });
        });
    }
    var deduplicated = [];
    var _loop_1 = function (option) {
        if (!deduplicated.some(function (obj) { return obj.value === option.value; })) {
            deduplicated.push(option);
        }
    };
    for (var _i = 0, _selected_1 = _selected; _i < _selected_1.length; _i++) {
        var option = _selected_1[_i];
        _loop_1(option);
    }
    return deduplicated;
};

var CMultiSelectOptions = React$1.forwardRef(function (_a, ref) {
    var handleOptionOnClick = _a.handleOptionOnClick, loading = _a.loading, options = _a.options, optionsMaxHeight = _a.optionsMaxHeight, optionsStyle = _a.optionsStyle, optionsTemplate = _a.optionsTemplate, optionsGroupsTemplate = _a.optionsGroupsTemplate, searchNoResultsLabel = _a.searchNoResultsLabel, selected = _a.selected, virtualScroller = _a.virtualScroller, _b = _a.visibleItems, visibleItems = _b === void 0 ? 10 : _b;
    var handleKeyDown = function (event, option) {
        if (event.code === 'Space' || event.key === 'Enter') {
            event.preventDefault();
            handleOptionOnClick && handleOptionOnClick(option);
        }
        if (event.key === 'Down' || event.key === 'ArrowDown') {
            event.preventDefault();
            var target = event.target;
            var next = getNextSibling(target, '.form-multi-select-option');
            next && next.focus();
        }
        if (event.key === 'Up' || event.key === 'ArrowUp') {
            event.preventDefault();
            var target = event.target;
            var prev = getPreviousSibling(target, '.form-multi-select-option');
            prev && prev.focus();
        }
    };
    var createOptions = function (options) {
        return options.length > 0 ? (options.map(function (option, index) {
            return 'value' in option ? (React$1.createElement("div", { className: classNames$1('form-multi-select-option', {
                    'form-multi-select-option-with-checkbox': optionsStyle === 'checkbox',
                    'form-multi-selected': selected.some(function (_option) { return _option.value === option.value; }),
                    disabled: option.disabled,
                }), key: index, onClick: function () { return handleOptionOnClick && handleOptionOnClick(option); }, onKeyDown: function (event) { return handleKeyDown(event, option); }, tabIndex: 0 }, optionsTemplate ? optionsTemplate(option) : option.text)) : (React$1.createElement("div", { className: "form-multi-select-optgroup-label", key: index }, optionsGroupsTemplate ? optionsGroupsTemplate(option) : option.label));
        })) : (React$1.createElement("div", { className: "form-multi-select-options-empty" }, searchNoResultsLabel));
    };
    return (React$1.createElement(React$1.Fragment, null,
        virtualScroller ? (React$1.createElement(CVirtualScroller, { className: "form-multi-select-options", visibleItems: visibleItems, ref: ref }, createOptions(options))) : (React$1.createElement("div", __assign$1({ className: "form-multi-select-options" }, (optionsMaxHeight !== 'auto' && {
            style: { maxHeight: optionsMaxHeight, overflow: 'scroll' },
        }), { ref: ref }), createOptions(options))),
        loading && React$1.createElement(CElementCover, null)));
});
CMultiSelectOptions.propTypes = {
    handleOptionOnClick: PropTypes$1.func,
    loading: PropTypes$1.bool,
    options: PropTypes$1.array.isRequired,
    optionsMaxHeight: PropTypes$1.oneOfType([PropTypes$1.number, PropTypes$1.string]),
    optionsStyle: PropTypes$1.oneOf(['checkbox', 'text']),
    optionsTemplate: PropTypes$1.func,
    optionsGroupsTemplate: PropTypes$1.func,
    searchNoResultsLabel: PropTypes$1.oneOfType([PropTypes$1.string, PropTypes$1.node]),
    virtualScroller: PropTypes$1.bool,
    visibleItems: PropTypes$1.number,
};
CMultiSelectOptions.displayName = 'CMultiSelectOptions';

var CMultiSelectSelection = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, multiple = _a.multiple, placeholder = _a.placeholder, onRemove = _a.onRemove, search = _a.search, _b = _a.selected, selected = _b === void 0 ? [] : _b, selectionType = _a.selectionType, selectionTypeCounterText = _a.selectionTypeCounterText;
    return (React$1.createElement("span", { className: classNames$1('form-multi-select-selection', {
            'form-multi-select-selection-tags': multiple && selectionType === 'tags',
        }), ref: ref },
        multiple && selectionType === 'counter' && !search && selected.length === 0 && placeholder,
        multiple &&
            selectionType === 'counter' &&
            !search &&
            selected.length > 0 &&
            "".concat(selected.length, " ").concat(selectionTypeCounterText),
        multiple &&
            selectionType === 'tags' &&
            selected.map(function (option, index) {
                if (selectionType === 'tags') {
                    return (React$1.createElement("span", { className: "form-multi-select-tag", key: index },
                        option.text,
                        !option.disabled && (React$1.createElement("button", { className: "form-multi-select-tag-delete", "aria-label": "Close", onClick: function () { return onRemove && onRemove(option); } },
                            React$1.createElement("span", { "aria-hidden": "true" }, "\u00D7")))));
                }
                return;
            }),
        multiple &&
            selectionType === 'text' &&
            selected.map(function (option, index) { return (React$1.createElement("span", { key: index },
                option.text,
                index === selected.length - 1 ? '' : ',',
                "\u00A0")); }),
        !multiple && !search && selected.map(function (option) { return option.text; })[0],
        children));
});
CMultiSelectSelection.propTypes = {
    multiple: PropTypes$1.bool,
    onRemove: PropTypes$1.func,
    placeholder: PropTypes$1.string,
    search: PropTypes$1.oneOfType([PropTypes$1.bool, PropTypes$1.oneOf(['external'])]),
    selected: PropTypes$1.array,
    selectionType: PropTypes$1.oneOf(['counter', 'tags', 'text']),
    selectionTypeCounterText: PropTypes$1.string,
};
CMultiSelectSelection.displayName = 'CMultiSelectSelection';

var CMultiSelect = React$1.forwardRef(function (_a, ref) {
    var _b;
    var allowCreateOptions = _a.allowCreateOptions, className = _a.className, _c = _a.cleaner, cleaner = _c === void 0 ? true : _c, clearSearchOnSelect = _a.clearSearchOnSelect, disabled = _a.disabled, feedback = _a.feedback, feedbackInvalid = _a.feedbackInvalid, feedbackValid = _a.feedbackValid, loading = _a.loading, _d = _a.multiple, multiple = _d === void 0 ? true : _d, id = _a.id, invalid = _a.invalid, label = _a.label, onChange = _a.onChange, onFilterChange = _a.onFilterChange, onHide = _a.onHide, onShow = _a.onShow, options = _a.options, _e = _a.optionsMaxHeight, optionsMaxHeight = _e === void 0 ? 'auto' : _e, _f = _a.optionsStyle, optionsStyle = _f === void 0 ? 'checkbox' : _f, optionsTemplate = _a.optionsTemplate, optionsGroupsTemplate = _a.optionsGroupsTemplate, _g = _a.placeholder, placeholder = _g === void 0 ? 'Select...' : _g, required = _a.required, _h = _a.search, search = _h === void 0 ? true : _h, _j = _a.searchNoResultsLabel, searchNoResultsLabel = _j === void 0 ? 'No results found' : _j, _k = _a.selectAll, selectAll = _k === void 0 ? true : _k, _l = _a.selectAllLabel, selectAllLabel = _l === void 0 ? 'Select all options' : _l, _m = _a.selectionType, selectionType = _m === void 0 ? 'tags' : _m, _o = _a.selectionTypeCounterText, selectionTypeCounterText = _o === void 0 ? 'item(s) selected' : _o, size = _a.size, text = _a.text, tooltipFeedback = _a.tooltipFeedback, valid = _a.valid, virtualScroller = _a.virtualScroller, _p = _a.visible, visible = _p === void 0 ? false : _p, _q = _a.visibleItems, visibleItems = _q === void 0 ? 10 : _q, rest = __rest$1(_a, ["allowCreateOptions", "className", "cleaner", "clearSearchOnSelect", "disabled", "feedback", "feedbackInvalid", "feedbackValid", "loading", "multiple", "id", "invalid", "label", "onChange", "onFilterChange", "onHide", "onShow", "options", "optionsMaxHeight", "optionsStyle", "optionsTemplate", "optionsGroupsTemplate", "placeholder", "required", "search", "searchNoResultsLabel", "selectAll", "selectAllLabel", "selectionType", "selectionTypeCounterText", "size", "text", "tooltipFeedback", "valid", "virtualScroller", "visible", "visibleItems"]);
    var multiSelectRef = React$1.useRef(null);
    var multiSelectForkedRef = useForkedRef(ref, multiSelectRef);
    var dropdownRef = React$1.useRef(null);
    var nativeSelectRef = React$1.useRef(null);
    var togglerRef = React$1.useRef(null);
    var searchRef = React$1.useRef(null);
    var isInitialMount = React$1.useRef(true);
    var _r = usePopper(), popper = _r.popper, initPopper = _r.initPopper, destroyPopper = _r.destroyPopper;
    var _s = React$1.useState(options), _options = _s[0], setOptions = _s[1];
    var _t = React$1.useState(visible), _visible = _t[0], setVisible = _t[1];
    var _u = React$1.useState(''), searchValue = _u[0], setSearchValue = _u[1];
    var _v = React$1.useState([]), selected = _v[0], setSelected = _v[1];
    var _w = React$1.useState([]), userOptions = _w[0], setUserOptions = _w[1];
    var filteredOptions = React$1.useMemo(function () {
        return flattenOptionsArray(search === 'external'
            ? __spreadArray(__spreadArray([], _options, true), filterOptionsList(searchValue, userOptions), true) : filterOptionsList(searchValue, __spreadArray(__spreadArray([], _options, true), userOptions, true)), true);
    }, [_options, searchValue, userOptions]);
    var flattenedOptions = React$1.useMemo(function () { return flattenOptionsArray(options); }, [JSON.stringify(options)]);
    var userOption = React$1.useMemo(function () {
        if (allowCreateOptions &&
            filteredOptions.some(function (option) { return option.text && option.text.toLowerCase() === searchValue.toLowerCase(); })) {
            return false;
        }
        return searchRef.current && createOption(String(searchValue), flattenedOptions);
    }, [filteredOptions, searchValue]);
    var popperConfig = {
        placement: (isRTL(multiSelectRef.current) ? 'bottom-end' : 'bottom-start'),
        modifiers: [
            {
                name: 'preventOverflow',
                options: {
                    boundary: 'clippingParents',
                },
            },
            {
                name: 'offset',
                options: {
                    offset: [0, 2],
                },
            },
        ],
    };
    React$1.useEffect(function () {
        setOptions(options);
        var _selected = flattenedOptions.filter(function (option) { return option.selected === true; });
        var deselected = flattenedOptions.filter(function (option) { return option.selected === false; });
        _selected && setSelected(selectOptions(_selected, selected, deselected));
    }, [JSON.stringify(options)]);
    React$1.useEffect(function () {
        !isInitialMount.current && onFilterChange && onFilterChange(searchValue);
    }, [searchValue]);
    React$1.useEffect(function () {
        if (!isInitialMount.current && nativeSelectRef.current) {
            nativeSelectRef.current.dispatchEvent(new Event('change', { bubbles: true }));
        }
        if (popper) {
            popper.update();
        }
    }, [JSON.stringify(selected)]);
    React$1.useEffect(function () {
        if (_visible) {
            onShow && onShow();
            window.addEventListener('mouseup', handleMouseUp);
            window.addEventListener('keyup', handleKeyUp);
            togglerRef.current &&
                dropdownRef.current &&
                initPopper(togglerRef.current, dropdownRef.current, popperConfig);
            searchRef.current && searchRef.current.focus();
        }
        return function () {
            onHide && onHide();
            window.removeEventListener('mouseup', handleMouseUp);
            window.removeEventListener('keyup', handleKeyUp);
            destroyPopper();
        };
    }, [_visible]);
    React$1.useEffect(function () {
        isInitialMount.current = false;
    }, []);
    var handleKeyUp = function (event) {
        if (event.key === 'Escape') {
            setVisible(false);
        }
    };
    var handleMouseUp = function (event) {
        if (multiSelectRef.current && multiSelectRef.current.contains(event.target)) {
            return;
        }
        setVisible(false);
    };
    var handleSearchChange = function (event) {
        var value = event.target.value;
        setSearchValue(value);
    };
    var handleSearchKeyDown = function (event) {
        if (event.key === 'Enter' && searchValue && allowCreateOptions) {
            event.preventDefault();
            if (userOption) {
                setSelected(__spreadArray(__spreadArray([], selected, true), userOption, true));
                setUserOptions(__spreadArray(__spreadArray([], userOptions, true), userOption, true));
            }
            if (!userOption) {
                setSelected(__spreadArray(__spreadArray([], selected, true), [
                    filteredOptions.find(function (option) { return String(option.text).toLowerCase() === searchValue.toLowerCase(); }),
                ], false));
            }
            setSearchValue('');
            if (searchRef.current) {
                searchRef.current.value = '';
            }
            return;
        }
        if (searchValue.length > 0) {
            return;
        }
        if (event.key === 'Backspace' || event.key === 'Delete') {
            var last_1 = selected.filter(function (option) { return !option.disabled; }).pop();
            last_1 && setSelected(selected.filter(function (option) { return option.value !== last_1.value; }));
        }
    };
    var handleOptionOnClick = function (option) {
        if (!multiple) {
            setSelected([option]);
            setVisible(false);
            setSearchValue('');
            if (searchRef.current) {
                searchRef.current.value = '';
            }
            return;
        }
        if (option.custom && !userOptions.some(function (_option) { return _option.value === option.value; })) {
            setUserOptions(__spreadArray(__spreadArray([], userOptions, true), [option], false));
        }
        if (clearSearchOnSelect || option.custom) {
            setSearchValue('');
            if (searchRef.current) {
                searchRef.current.value = '';
                searchRef.current.focus();
            }
        }
        if (selected.some(function (_option) { return _option.value === option.value; })) {
            setSelected(selected.filter(function (_option) { return _option.value !== option.value; }));
        }
        else {
            setSelected(__spreadArray(__spreadArray([], selected, true), [option], false));
        }
    };
    var handleSelectAll = function () {
        setSelected(selectOptions(__spreadArray(__spreadArray([], flattenedOptions.filter(function (option) { return !option.disabled; }), true), userOptions, true), selected));
    };
    var handleDeselectAll = function () {
        setSelected(selected.filter(function (option) { return option.disabled; }));
    };
    return (React$1.createElement(CFormControlWrapper, { describedby: rest['aria-describedby'], feedback: feedback, feedbackInvalid: feedbackInvalid, feedbackValid: feedbackValid, id: id, invalid: invalid, label: label, text: text, tooltipFeedback: tooltipFeedback, valid: valid },
        React$1.createElement(CMultiSelectNativeSelect, { className: 'form-multi-select', id: id, multiple: multiple, options: selected, required: required, value: multiple
                ? selected.map(function (option) { return option.value.toString(); })
                : selected.map(function (option) { return option.value; })[0], onChange: function () { return onChange && onChange(selected); }, ref: nativeSelectRef }),
        React$1.createElement("div", { className: classNames$1('form-multi-select', (_b = {
                    'form-multi-select-with-cleaner': cleaner
                },
                _b["form-multi-select-".concat(size)] = size,
                _b['form-multi-select-selection-tags'] = multiple && selectionType === 'tags',
                _b.disabled = disabled,
                _b['is-invalid'] = invalid,
                _b['is-valid'] = valid,
                _b.show = _visible,
                _b), className), "aria-expanded": _visible, id: id, ref: multiSelectForkedRef },
            React$1.createElement("div", { className: "form-multi-select-input-group", onClick: function () { return setVisible(true); }, ref: togglerRef },
                React$1.createElement(CMultiSelectSelection, { multiple: multiple, onRemove: function (option) { return !disabled && handleOptionOnClick(option); }, placeholder: placeholder, search: search, selected: selected, selectionType: selectionType, selectionTypeCounterText: selectionTypeCounterText }, search && (React$1.createElement("input", __assign$1({ type: "text", className: "form-multi-select-search", disabled: disabled, autoComplete: "off", onChange: handleSearchChange, onKeyDown: handleSearchKeyDown }, (selected.length === 0 && { placeholder: placeholder }), (selected.length > 0 &&
                    selectionType === 'counter' && {
                    placeholder: "".concat(selected.length, " ").concat(selectionTypeCounterText),
                }), (selected.length > 0 &&
                    !multiple && { placeholder: selected.map(function (option) { return option.text; })[0] }), (multiple &&
                    selected.length > 0 &&
                    selectionType !== 'counter' && { size: searchValue.length + 2 }), { ref: searchRef })))),
                !disabled && cleaner && selected.length > 0 && (React$1.createElement("button", { type: "button", className: "form-multi-select-selection-cleaner", onClick: function () { return handleDeselectAll(); } }))),
            React$1.createElement("div", { className: "form-multi-select-dropdown", role: "menu", ref: dropdownRef },
                multiple && selectAll && (React$1.createElement("button", { type: "button", className: "form-multi-select-all", onClick: function () { return handleSelectAll(); } }, selectAllLabel)),
                React$1.createElement(CMultiSelectOptions, { handleOptionOnClick: function (option) { return !disabled && handleOptionOnClick(option); }, loading: loading, options: filteredOptions.length === 0 && allowCreateOptions
                        ? userOption || []
                        : filteredOptions, optionsMaxHeight: optionsMaxHeight, optionsStyle: optionsStyle, optionsTemplate: optionsTemplate, optionsGroupsTemplate: optionsGroupsTemplate, searchNoResultsLabel: searchNoResultsLabel, selected: selected, virtualScroller: virtualScroller, visibleItems: visibleItems })))));
});
CMultiSelect.propTypes = __assign$1({ className: PropTypes$1.string, cleaner: PropTypes$1.bool, clearSearchOnSelect: PropTypes$1.bool, disabled: PropTypes$1.bool, loading: PropTypes$1.bool, multiple: PropTypes$1.bool, onChange: PropTypes$1.func, onFilterChange: PropTypes$1.func, onHide: PropTypes$1.func, onShow: PropTypes$1.func, options: PropTypes$1.array.isRequired, optionsMaxHeight: PropTypes$1.oneOfType([PropTypes$1.number, PropTypes$1.string]), optionsStyle: PropTypes$1.oneOf(['checkbox', 'text']), optionsTemplate: PropTypes$1.func, optionsGroupsTemplate: PropTypes$1.func, placeholder: PropTypes$1.string, required: PropTypes$1.bool, search: PropTypes$1.oneOfType([PropTypes$1.bool, PropTypes$1.oneOf(['external'])]), searchNoResultsLabel: PropTypes$1.oneOfType([PropTypes$1.string, PropTypes$1.node]), selectAll: PropTypes$1.bool, selectAllLabel: PropTypes$1.oneOfType([PropTypes$1.string, PropTypes$1.node]), selectionType: PropTypes$1.oneOf(['counter', 'tags', 'text']), selectionTypeCounterText: PropTypes$1.string, size: PropTypes$1.oneOf(['sm', 'lg']), virtualScroller: PropTypes$1.bool, visible: PropTypes$1.bool, visibleItems: PropTypes$1.number }, CFormControlWrapper.propTypes);
CMultiSelect.displayName = 'CMultiSelect';

var CNav = React$1.forwardRef(function (_a, ref) {
    var _b;
    var children = _a.children, className = _a.className, _c = _a.component, Component = _c === void 0 ? 'ul' : _c, layout = _a.layout, variant = _a.variant, rest = __rest$1(_a, ["children", "className", "component", "layout", "variant"]);
    return (React$1.createElement(Component, __assign$1({ className: classNames$1('nav', (_b = {},
            _b["nav-".concat(layout)] = layout,
            _b["nav-".concat(variant)] = variant,
            _b), className), role: "navigation" }, rest, { ref: ref }), children));
});
CNav.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    component: PropTypes$1.elementType,
    layout: PropTypes$1.oneOf(['fill', 'justified']),
    variant: PropTypes$1.oneOf(['tabs', 'pills', 'underline']),
};
CNav.displayName = 'CNav';

var CNavGroupItems = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, rest = __rest$1(_a, ["children", "className"]);
    return (React$1.createElement("ul", __assign$1({ className: classNames$1('nav-group-items', className) }, rest, { ref: ref }), children));
});
CNavGroupItems.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
};
CNavGroupItems.displayName = 'CNavGroupItems';

var CNavContext = React$1.createContext({});
var CSidebarNav = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, rest = __rest$1(_a, ["children", "className"]);
    var _b = React$1.useState(''), visibleGroup = _b[0], setVisibleGroup = _b[1];
    var CNavContextValues = {
        visibleGroup: visibleGroup,
        setVisibleGroup: setVisibleGroup,
    };
    return (React$1.createElement("ul", __assign$1({ className: classNames$1('sidebar-nav', className), ref: ref }, rest),
        React$1.createElement(CNavContext.Provider, { value: CNavContextValues }, React$1.Children.map(children, function (child, index) {
            if (React$1.isValidElement(child)) {
                return React$1.cloneElement(child, {
                    key: index,
                    idx: "".concat(index),
                });
            }
            return;
        }))));
});
CSidebarNav.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
};
CSidebarNav.displayName = 'CSidebarNav';

var isInVisibleGroup = function (el1, el2) {
    var array1 = el1.toString().split('.');
    var array2 = el2.toString().split('.');
    return array2.every(function (item, index) { return item === array1[index]; });
};
var CNavGroup = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, compact = _a.compact, idx = _a.idx, toggler = _a.toggler, visible = _a.visible, rest = __rest$1(_a, ["children", "className", "compact", "idx", "toggler", "visible"]);
    var _b = React$1.useState(), height = _b[0], setHeight = _b[1];
    var navItemsRef = React$1.useRef(null);
    var _c = React$1.useContext(CNavContext), visibleGroup = _c.visibleGroup, setVisibleGroup = _c.setVisibleGroup;
    var _d = React$1.useState(Boolean(visible || (idx && visibleGroup && isInVisibleGroup(visibleGroup, idx)))), _visible = _d[0], setVisible = _d[1];
    React$1.useEffect(function () {
        setVisible(Boolean(idx && visibleGroup && isInVisibleGroup(visibleGroup, idx)));
    }, [visibleGroup]);
    var handleTogglerOnCLick = function (event) {
        event.preventDefault();
        setVisibleGroup(_visible ? ((idx === null || idx === void 0 ? void 0 : idx.toString().includes('.')) ? idx.slice(0, idx.lastIndexOf('.')) : '') : idx);
        setVisible(!_visible);
    };
    var style = {
        height: 0,
    };
    var onEntering = function () {
        navItemsRef.current && setHeight(navItemsRef.current.scrollHeight);
    };
    var onEntered = function () {
        setHeight('auto');
    };
    var onExit = function () {
        navItemsRef.current && setHeight(navItemsRef.current.scrollHeight);
    };
    var onExiting = function () {
        var _a;
        // @ts-expect-error reflow is necessary to get correct height of the element
        // eslint-disable-next-line @typescript-eslint/no-unused-vars
        (_a = navItemsRef.current) === null || _a === void 0 ? void 0 : _a.offsetHeight;
        setHeight(0);
    };
    var onExited = function () {
        setHeight(0);
    };
    var transitionStyles = {
        entering: { display: 'block', height: height },
        entered: { display: 'block', height: height },
        exiting: { display: 'block', height: height },
        exited: { height: height },
    };
    return (React$1.createElement("li", __assign$1({ className: classNames$1('nav-group', { show: _visible }, className) }, rest, { ref: ref }),
        toggler && (React$1.createElement("a", { className: "nav-link nav-group-toggle", onClick: function (event) { return handleTogglerOnCLick(event); } }, toggler)),
        React$1.createElement(Transition$1, { in: _visible, nodeRef: navItemsRef, onEntering: onEntering, onEntered: onEntered, onExit: onExit, onExiting: onExiting, onExited: onExited, timeout: 300 }, function (state) { return (React$1.createElement("ul", { className: classNames$1('nav-group-items', {
                compact: compact,
            }), style: __assign$1(__assign$1({}, style), transitionStyles[state]), ref: navItemsRef }, React$1.Children.map(children, function (child, index) {
            if (React$1.isValidElement(child)) {
                return React$1.cloneElement(child, {
                    key: index,
                    idx: "".concat(idx, ".").concat(index),
                });
            }
            return;
        }))); })));
});
CNavGroup.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    compact: PropTypes$1.bool,
    idx: PropTypes$1.string,
    toggler: PropTypes$1.oneOfType([PropTypes$1.string, PropTypes$1.node]),
    visible: PropTypes$1.bool,
};
CNavGroup.displayName = 'CNavGroup';

var CNavLink = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, idx = _a.idx, rest = __rest$1(_a, ["children", "className", "idx"]);
    var navLinkRef = React$1.useRef(null);
    var forkedRef = useForkedRef(ref, navLinkRef);
    var setVisibleGroup = React$1.useContext(CNavContext).setVisibleGroup;
    React$1.useEffect(function () {
        var _a;
        rest.active = (_a = navLinkRef.current) === null || _a === void 0 ? void 0 : _a.classList.contains('active');
        idx && rest.active && setVisibleGroup(idx);
    }, [rest.active, className]);
    return (React$1.createElement(CLink, __assign$1({ className: classNames$1('nav-link', className) }, rest, { ref: forkedRef }), children));
});
CNavLink.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    idx: PropTypes$1.string,
};
CNavLink.displayName = 'CNavLink';

var CNavItem = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, rest = __rest$1(_a, ["children", "className"]);
    return (React$1.createElement("li", { className: classNames$1('nav-item', className), ref: ref }, rest.href || rest.to ? (React$1.createElement(CNavLink, __assign$1({ className: className }, rest), children)) : (children)));
});
CNavItem.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
};
CNavItem.displayName = 'CNavItem';

var CNavTitle = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, rest = __rest$1(_a, ["children", "className"]);
    return (React$1.createElement("li", __assign$1({ className: classNames$1('nav-title', className) }, rest, { ref: ref }), children));
});
CNavTitle.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
};
CNavTitle.displayName = 'CNavTitle';

var CNavbar = React$1.forwardRef(function (_a, ref) {
    var _b;
    var children = _a.children, className = _a.className, color = _a.color, colorScheme = _a.colorScheme, _c = _a.component, Component = _c === void 0 ? 'nav' : _c, container = _a.container, expand = _a.expand, placement = _a.placement, rest = __rest$1(_a, ["children", "className", "color", "colorScheme", "component", "container", "expand", "placement"]);
    return (React$1.createElement(Component, __assign$1({ className: classNames$1('navbar', (_b = {},
            _b["bg-".concat(color)] = color,
            _b["navbar-".concat(colorScheme)] = colorScheme,
            _b[typeof expand === 'boolean' ? 'navbar-expand' : "navbar-expand-".concat(expand)] = expand,
            _b), placement, className) }, rest, { ref: ref }), container ? (React$1.createElement("div", { className: typeof container === 'string' ? "container-".concat(container) : 'container' }, children)) : (React$1.createElement(React$1.Fragment, null, children))));
});
CNavbar.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    color: colorPropType,
    colorScheme: PropTypes$1.oneOf(['dark', 'light']),
    component: PropTypes$1.elementType,
    container: PropTypes$1.oneOfType([
        PropTypes$1.bool,
        PropTypes$1.oneOf([
            'sm',
            'md',
            'lg',
            'xl',
            'xxl',
            'fluid',
        ]),
    ]),
    expand: PropTypes$1.oneOfType([
        PropTypes$1.bool,
        PropTypes$1.oneOf(['sm', 'md', 'lg', 'xl', 'xxl']),
    ]),
    placement: PropTypes$1.oneOf(['fixed-top', 'fixed-bottom', 'sticky-top']),
};
CNavbar.displayName = 'CNavbar';

var CNavbarBrand = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, component = _a.component, className = _a.className, rest = __rest$1(_a, ["children", "component", "className"]);
    var Component = component !== null && component !== void 0 ? component : (rest.href ? 'a' : 'span');
    return (React$1.createElement(Component, __assign$1({ className: classNames$1('navbar-brand', className) }, rest, { ref: ref }), children));
});
CNavbarBrand.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    component: PropTypes$1.elementType,
};
CNavbarBrand.displayName = 'CNavbarBrand';

var CNavbarNav = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, _b = _a.component, Component = _b === void 0 ? 'ul' : _b, className = _a.className, rest = __rest$1(_a, ["children", "component", "className"]);
    return (React$1.createElement(Component, __assign$1({ className: classNames$1('navbar-nav', className), role: "navigation" }, rest, { ref: ref }), children));
});
CNavbarNav.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    component: PropTypes$1.elementType,
};
CNavbarNav.displayName = 'CNavbarNav';

var CNavbarText = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, rest = __rest$1(_a, ["children", "className"]);
    return (React$1.createElement("span", __assign$1({ className: classNames$1('navbar-text', className) }, rest, { ref: ref }), children));
});
CNavbarText.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
};
CNavbarText.displayName = 'CNavbarText';

var CNavbarToggler = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, rest = __rest$1(_a, ["children", "className"]);
    return (React$1.createElement("button", __assign$1({ type: "button", className: classNames$1('navbar-toggler', className) }, rest, { ref: ref }), children !== null && children !== void 0 ? children : React$1.createElement("span", { className: "navbar-toggler-icon" })));
});
CNavbarToggler.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
};
CNavbarToggler.displayName = 'CNavbarToggler';

var COffcanvas = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, _b = _a.backdrop, backdrop = _b === void 0 ? true : _b, className = _a.className, _c = _a.keyboard, keyboard = _c === void 0 ? true : _c, onHide = _a.onHide, onShow = _a.onShow, placement = _a.placement, _d = _a.portal, portal = _d === void 0 ? false : _d, _e = _a.responsive, responsive = _e === void 0 ? true : _e, _f = _a.scroll, scroll = _f === void 0 ? false : _f, _g = _a.visible, visible = _g === void 0 ? false : _g, rest = __rest$1(_a, ["children", "backdrop", "className", "keyboard", "onHide", "onShow", "placement", "portal", "responsive", "scroll", "visible"]);
    var _h = React$1.useState(visible), _visible = _h[0], setVisible = _h[1];
    var offcanvasRef = React$1.useRef(null);
    var forkedRef = useForkedRef(ref, offcanvasRef);
    React$1.useEffect(function () {
        setVisible(visible);
    }, [visible]);
    React$1.useEffect(function () {
        if (_visible && !scroll) {
            document.body.style.overflow = 'hidden';
            document.body.style.paddingRight = '0px';
            return;
        }
        if (!scroll) {
            document.body.style.removeProperty('overflow');
            document.body.style.removeProperty('padding-right');
        }
    }, [_visible]);
    var handleDismiss = function () {
        setVisible(false);
    };
    var handleBackdropDismiss = function () {
        if (backdrop !== 'static') {
            setVisible(false);
        }
    };
    var handleKeyDown = function (event) {
        if (event.key === 'Escape' && keyboard) {
            return handleDismiss();
        }
    };
    return (React$1.createElement(React$1.Fragment, null,
        React$1.createElement(Transition$1, { in: _visible, nodeRef: offcanvasRef, onEnter: onShow, onEntered: function () { var _a; return (_a = offcanvasRef.current) === null || _a === void 0 ? void 0 : _a.focus(); }, onExit: onHide, timeout: 300 }, function (state) {
            var _a;
            return (React$1.createElement(CConditionalPortal, { portal: portal },
                React$1.createElement("div", __assign$1({ className: classNames$1((_a = {},
                        _a["offcanvas".concat(typeof responsive === 'string' ? '-' + responsive : '')] = responsive,
                        _a["offcanvas-".concat(placement)] = placement,
                        _a.showing = state === 'entering',
                        _a.show = state === 'entered',
                        _a['show hiding'] = state === 'exiting',
                        _a), className), role: "dialog", tabIndex: -1, onKeyDown: handleKeyDown }, rest, { ref: forkedRef }), children)));
        }),
        backdrop && (React$1.createElement(CConditionalPortal, { portal: portal },
            React$1.createElement(CBackdrop, { className: "offcanvas-backdrop", onClick: handleBackdropDismiss, visible: _visible })))));
});
COffcanvas.propTypes = {
    backdrop: PropTypes$1.oneOfType([PropTypes$1.bool, PropTypes$1.oneOf(['static'])]),
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    keyboard: PropTypes$1.bool,
    onHide: PropTypes$1.func,
    onShow: PropTypes$1.func,
    placement: PropTypes$1.oneOf(['start', 'end', 'top', 'bottom'])
        .isRequired,
    portal: PropTypes$1.bool,
    responsive: PropTypes$1.oneOfType([
        PropTypes$1.bool,
        PropTypes$1.oneOf(['sm', 'md', 'lg', 'xl', 'xxl']),
    ]),
    scroll: PropTypes$1.bool,
    visible: PropTypes$1.bool,
};
COffcanvas.displayName = 'COffcanvas';

var COffcanvasBody = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, rest = __rest$1(_a, ["children", "className"]);
    return (React$1.createElement("div", __assign$1({ className: classNames$1('offcanvas-body', className) }, rest, { ref: ref }), children));
});
COffcanvasBody.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
};
COffcanvasBody.displayName = 'COffcanvasBody';

var COffcanvasHeader = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, rest = __rest$1(_a, ["children", "className"]);
    return (React$1.createElement("div", __assign$1({ className: classNames$1('offcanvas-header', className) }, rest, { ref: ref }), children));
});
COffcanvasHeader.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
};
COffcanvasHeader.displayName = 'COffcanvasHeader';

var COffcanvasTitle = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, _b = _a.component, Component = _b === void 0 ? 'h5' : _b, className = _a.className, rest = __rest$1(_a, ["children", "component", "className"]);
    return (React$1.createElement(Component, __assign$1({ className: classNames$1('offcanvas-title', className) }, rest, { ref: ref }), children));
});
COffcanvasTitle.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    component: PropTypes$1.elementType,
};
COffcanvasTitle.displayName = 'COffcanvasTitle';

var CPagination = React$1.forwardRef(function (_a, ref) {
    var _b;
    var children = _a.children, align = _a.align, className = _a.className, size = _a.size, rest = __rest$1(_a, ["children", "align", "className", "size"]);
    return (React$1.createElement("nav", __assign$1({ ref: ref }, rest),
        React$1.createElement("ul", { className: classNames$1('pagination', (_b = {},
                _b["justify-content-".concat(align)] = align,
                _b["pagination-".concat(size)] = size,
                _b), className) }, children)));
});
CPagination.propTypes = {
    align: PropTypes$1.oneOf(['start', 'center', 'end']),
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    size: PropTypes$1.oneOf(['sm', 'lg']),
};
CPagination.displayName = 'CPagination';

var CPaginationItem = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, component = _a.component, rest = __rest$1(_a, ["children", "className", "component"]);
    var Component = component !== null && component !== void 0 ? component : (rest.active ? 'span' : 'a');
    return (React$1.createElement("li", __assign$1({ className: classNames$1('page-item', {
            active: rest.active,
            disabled: rest.disabled,
        }, className) }, (rest.active && { 'aria-current': 'page' })), Component === 'a' ? (React$1.createElement(CLink, __assign$1({ className: "page-link", component: Component }, rest, { ref: ref }), children)) : (React$1.createElement(Component, { className: "page-link", ref: ref }, children))));
});
CPaginationItem.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    component: PropTypes$1.elementType,
};
CPaginationItem.displayName = 'CPaginationItem';

var BREAKPOINTS = [
    'xxl',
    'xl',
    'lg',
    'md',
    'sm',
    'xs',
];
var CPlaceholder = React$1.forwardRef(function (_a, ref) {
    var _b;
    var children = _a.children, animation = _a.animation, className = _a.className, color = _a.color, _c = _a.component, Component = _c === void 0 ? 'span' : _c, size = _a.size, rest = __rest$1(_a, ["children", "animation", "className", "color", "component", "size"]);
    var repsonsiveClassNames = [];
    BREAKPOINTS.forEach(function (bp) {
        var breakpoint = rest[bp];
        delete rest[bp];
        var infix = bp === 'xs' ? '' : "-".concat(bp);
        if (typeof breakpoint === 'number') {
            repsonsiveClassNames.push("col".concat(infix, "-").concat(breakpoint));
        }
        if (typeof breakpoint === 'boolean') {
            repsonsiveClassNames.push("col".concat(infix));
        }
    });
    return (React$1.createElement(Component, __assign$1({ className: classNames$1(animation ? "placeholder-".concat(animation) : 'placeholder', (_b = {},
            _b["bg-".concat(color)] = color,
            _b["placeholder-".concat(size)] = size,
            _b), repsonsiveClassNames, className) }, rest, { ref: ref }), children));
});
CPlaceholder.propTypes = {
    animation: PropTypes$1.oneOf(['glow', 'wave']),
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    color: colorPropType,
    component: PropTypes$1.elementType,
    size: PropTypes$1.oneOf(['xs', 'sm', 'lg']),
};
CPlaceholder.displayName = 'CPlaceholder';

var CProgressStackedContext = React$1.createContext({});
var CProgressStacked = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, rest = __rest$1(_a, ["children", "className"]);
    return (React$1.createElement("div", __assign$1({ className: classNames$1('progress-stacked', className), ref: ref }, rest),
        React$1.createElement(CProgressStackedContext.Provider, { value: {
                stacked: true,
            } }, children)));
});
CProgressStacked.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
};
CProgressStacked.displayName = 'CProgressStacked';

var CProgressBar = React$1.forwardRef(function (_a, ref) {
    var _b;
    var children = _a.children, animated = _a.animated, className = _a.className, color = _a.color, _c = _a.value, value = _c === void 0 ? 0 : _c, variant = _a.variant, rest = __rest$1(_a, ["children", "animated", "className", "color", "value", "variant"]);
    var stacked = React$1.useContext(CProgressStackedContext).stacked;
    return (React$1.createElement("div", __assign$1({ className: classNames$1('progress-bar', (_b = {},
            _b["bg-".concat(color)] = color,
            _b["progress-bar-".concat(variant)] = variant,
            _b['progress-bar-animated'] = animated,
            _b), className) }, (!stacked && { style: { width: "".concat(value, "%") } }), rest, { ref: ref }), children));
});
CProgressBar.propTypes = {
    animated: PropTypes$1.bool,
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    color: PropTypes$1.oneOfType([colorPropType, gradientsPropType]),
    value: PropTypes$1.number,
    variant: PropTypes$1.oneOf(['striped']),
};
CProgressBar.displayName = 'CProgressBar';

var CProgress = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, height = _a.height, progressBarClassName = _a.progressBarClassName, thin = _a.thin, value = _a.value, white = _a.white, rest = __rest$1(_a, ["children", "className", "height", "progressBarClassName", "thin", "value", "white"]);
    var stacked = React$1.useContext(CProgressStackedContext).stacked;
    return (React$1.createElement("div", __assign$1({ className: classNames$1('progress', {
            'progress-thin': thin,
            'progress-white': white,
        }, className) }, (value !== undefined && {
        role: 'progressbar',
        'aria-valuenow': value,
        'aria-valuemin': 0,
        'aria-valuemax': 100,
    }), { style: __assign$1(__assign$1({}, (height ? { height: "".concat(height, "px") } : {})), (stacked ? { width: "".concat(value, "%") } : {})), ref: ref }), React$1.Children.toArray(children).some(
    // @ts-expect-error displayName is set in the CProgressBar component
    function (child) { return child.type && child.type.displayName === 'CProgressBar'; }) ? (React$1.Children.map(children, function (child) {
        // @ts-expect-error displayName is set in the CProgressBar component
        if (React$1.isValidElement(child) && child.type.displayName === 'CProgressBar') {
            return React$1.cloneElement(child, __assign$1(__assign$1({}, (value && { value: value })), rest));
        }
        return;
    })) : (React$1.createElement(CProgressBar, __assign$1({}, (progressBarClassName && { className: progressBarClassName }), { value: value }, rest), children))));
});
CProgress.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    height: PropTypes$1.number,
    progressBarClassName: PropTypes$1.string,
    thin: PropTypes$1.bool,
    value: PropTypes$1.number,
    white: PropTypes$1.bool,
};
CProgress.displayName = 'CProgress';

var CPopover = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, _b = _a.animation, animation = _b === void 0 ? true : _b, className = _a.className, container = _a.container, content = _a.content, _c = _a.delay, delay = _c === void 0 ? 0 : _c, _d = _a.fallbackPlacements, fallbackPlacements = _d === void 0 ? ['top', 'right', 'bottom', 'left'] : _d, _e = _a.offset, offset = _e === void 0 ? [0, 8] : _e, onHide = _a.onHide; _a.onShow; var _f = _a.placement, placement = _f === void 0 ? 'top' : _f, title = _a.title, _g = _a.trigger, trigger = _g === void 0 ? 'click' : _g, visible = _a.visible, rest = __rest$1(_a, ["children", "animation", "className", "container", "content", "delay", "fallbackPlacements", "offset", "onHide", "onShow", "placement", "title", "trigger", "visible"]);
    var popoverRef = React$1.useRef(null);
    var togglerRef = React$1.useRef(null);
    var forkedRef = useForkedRef(ref, popoverRef);
    var uID = React$1.useRef("popover".concat(Math.floor(Math.random() * 1000000)));
    var _h = usePopper(), initPopper = _h.initPopper, destroyPopper = _h.destroyPopper;
    var _j = React$1.useState(visible), _visible = _j[0], setVisible = _j[1];
    var _delay = typeof delay === 'number' ? { show: delay, hide: delay } : delay;
    var popperConfig = {
        modifiers: [
            {
                name: 'arrow',
                options: {
                    element: '.popover-arrow',
                },
            },
            {
                name: 'flip',
                options: {
                    fallbackPlacements: fallbackPlacements,
                },
            },
            {
                name: 'offset',
                options: {
                    offset: offset,
                },
            },
        ],
        placement: getRTLPlacement(placement, togglerRef.current),
    };
    React$1.useEffect(function () {
        setVisible(visible);
    }, [visible]);
    var toggleVisible = function (visible) {
        if (visible) {
            setTimeout(function () { return setVisible(true); }, _delay.show);
            return;
        }
        setTimeout(function () { return setVisible(false); }, _delay.hide);
    };
    return (React$1.createElement(React$1.Fragment, null,
        React$1.cloneElement(children, __assign$1(__assign$1(__assign$1(__assign$1(__assign$1({}, (_visible && {
            'aria-describedby': uID.current,
        })), { ref: togglerRef }), ((trigger === 'click' || trigger.includes('click')) && {
            onClick: function () { return toggleVisible(!_visible); },
        })), ((trigger === 'focus' || trigger.includes('focus')) && {
            onFocus: function () { return toggleVisible(true); },
            onBlur: function () { return toggleVisible(false); },
        })), ((trigger === 'hover' || trigger.includes('hover')) && {
            onMouseEnter: function () { return toggleVisible(true); },
            onMouseLeave: function () { return toggleVisible(false); },
        }))),
        React$1.createElement(CConditionalPortal, { container: container, portal: true },
            React$1.createElement(Transition$1, { in: _visible, mountOnEnter: true, nodeRef: popoverRef, onEnter: function () {
                    if (togglerRef.current && popoverRef.current) {
                        initPopper(togglerRef.current, popoverRef.current, popperConfig);
                    }
                }, onEntering: function () {
                    if (togglerRef.current && popoverRef.current) {
                        popoverRef.current.style.display = 'initial';
                    }
                }, onExit: onHide, onExited: function () {
                    destroyPopper();
                }, timeout: {
                    enter: 0,
                    exit: popoverRef.current
                        ? getTransitionDurationFromElement(popoverRef.current) + 50
                        : 200,
                }, unmountOnExit: true }, function (state) { return (React$1.createElement("div", __assign$1({ className: classNames$1('popover', 'bs-popover-auto', {
                    fade: animation,
                    show: state === 'entered',
                }, className), id: uID.current, ref: forkedRef, role: "tooltip", style: {
                    display: 'none',
                } }, rest),
                React$1.createElement("div", { className: "popover-arrow" }),
                React$1.createElement("div", { className: "popover-header" }, title),
                React$1.createElement("div", { className: "popover-body" }, content))); }))));
});
CPopover.propTypes = {
    animation: PropTypes$1.bool,
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    container: PropTypes$1.any,
    content: PropTypes$1.oneOfType([PropTypes$1.string, PropTypes$1.node]),
    delay: PropTypes$1.oneOfType([
        PropTypes$1.number,
        PropTypes$1.shape({
            show: PropTypes$1.number.isRequired,
            hide: PropTypes$1.number.isRequired,
        }),
    ]),
    fallbackPlacements: fallbackPlacementsPropType,
    offset: PropTypes$1.any,
    onHide: PropTypes$1.func,
    onShow: PropTypes$1.func,
    placement: PropTypes$1.oneOf(['auto', 'top', 'right', 'bottom', 'left']),
    title: PropTypes$1.oneOfType([PropTypes$1.string, PropTypes$1.node]),
    trigger: triggerPropType,
    visible: PropTypes$1.bool,
};
CPopover.displayName = 'CPopover';

var cilArrowBottom = ["512 512", "<polygon fill='var(--ci-primary-color, currentColor)' points='367.997 338.75 271.999 434.747 271.999 17.503 239.999 17.503 239.999 434.745 144.003 338.75 121.376 361.377 256 496 390.624 361.377 367.997 338.75' class='ci-primary'/>"];

var cilArrowTop = ["512 512", "<polygon fill='var(--ci-primary-color, currentColor)' points='390.624 150.625 256 16 121.376 150.625 144.004 173.252 240.001 77.254 240.001 495.236 272.001 495.236 272.001 77.257 367.996 173.252 390.624 150.625' class='ci-primary'/>"];

var cilFilterX = ["512 512", "<polygon fill='var(--ci-primary-color, currentColor)' points='40 16 40 53.828 109.024 136 150.815 136 76.896 48 459.51 48 304 242.388 304 401.373 241.373 464 240 464 240 368 208 368 208 496 254.627 496 336 414.627 336 253.612 496 53.612 496 16 40 16' class='ci-primary'/><polygon fill='var(--ci-primary-color, currentColor)' points='166.403 248.225 226.864 187.763 204.237 165.135 143.775 225.597 83.313 165.135 60.687 187.763 121.148 248.225 60.687 308.687 83.313 331.314 143.775 270.852 204.237 331.314 226.864 308.687 166.403 248.225' class='ci-primary'/>"];

var cilSwapVertical = ["512 512", "<polygon fill='var(--ci-primary-color, currentColor)' points='384 433.373 384 160 352 160 352 434.51 282.177 364.687 259.55 387.313 367.432 495.196 475.313 387.313 452.687 364.687 384 433.373' class='ci-primary'/><polygon fill='var(--ci-primary-color, currentColor)' points='159.432 17.372 51.55 125.255 74.177 147.882 144 78.059 144 352 176 352 176 79.195 244.687 147.882 267.313 125.255 159.432 17.372' class='ci-primary'/>"];

/******************************************************************************
Copyright (c) Microsoft Corporation.

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES WITH
REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF MERCHANTABILITY
AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY SPECIAL, DIRECT,
INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES WHATSOEVER RESULTING FROM
LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION OF CONTRACT, NEGLIGENCE OR
OTHER TORTIOUS ACTION, ARISING OUT OF OR IN CONNECTION WITH THE USE OR
PERFORMANCE OF THIS SOFTWARE.
***************************************************************************** */
/* global Reflect, Promise, SuppressedError, Symbol */


var __assign = function() {
    __assign = Object.assign || function __assign(t) {
        for (var s, i = 1, n = arguments.length; i < n; i++) {
            s = arguments[i];
            for (var p in s) if (Object.prototype.hasOwnProperty.call(s, p)) t[p] = s[p];
        }
        return t;
    };
    return __assign.apply(this, arguments);
};

function __rest(s, e) {
    var t = {};
    for (var p in s) if (Object.prototype.hasOwnProperty.call(s, p) && e.indexOf(p) < 0)
        t[p] = s[p];
    if (s != null && typeof Object.getOwnPropertySymbols === "function")
        for (var i = 0, p = Object.getOwnPropertySymbols(s); i < p.length; i++) {
            if (e.indexOf(p[i]) < 0 && Object.prototype.propertyIsEnumerable.call(s, p[i]))
                t[p[i]] = s[p[i]];
        }
    return t;
}

typeof SuppressedError === "function" ? SuppressedError : function (error, suppressed, message) {
    var e = new Error(message);
    return e.name = "SuppressedError", e.error = error, e.suppressed = suppressed, e;
};

function getDefaultExportFromCjs (x) {
	return x && x.__esModule && Object.prototype.hasOwnProperty.call(x, 'default') ? x['default'] : x;
}

var propTypes = {exports: {}};

var reactIs = {exports: {}};

var reactIs_production_min = {};

/** @license React v16.13.1
 * react-is.production.min.js
 *
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

var hasRequiredReactIs_production_min;

function requireReactIs_production_min () {
	if (hasRequiredReactIs_production_min) return reactIs_production_min;
	hasRequiredReactIs_production_min = 1;
var b="function"===typeof Symbol&&Symbol.for,c=b?Symbol.for("react.element"):60103,d=b?Symbol.for("react.portal"):60106,e=b?Symbol.for("react.fragment"):60107,f=b?Symbol.for("react.strict_mode"):60108,g=b?Symbol.for("react.profiler"):60114,h=b?Symbol.for("react.provider"):60109,k=b?Symbol.for("react.context"):60110,l=b?Symbol.for("react.async_mode"):60111,m=b?Symbol.for("react.concurrent_mode"):60111,n=b?Symbol.for("react.forward_ref"):60112,p=b?Symbol.for("react.suspense"):60113,q=b?
	Symbol.for("react.suspense_list"):60120,r=b?Symbol.for("react.memo"):60115,t=b?Symbol.for("react.lazy"):60116,v=b?Symbol.for("react.block"):60121,w=b?Symbol.for("react.fundamental"):60117,x=b?Symbol.for("react.responder"):60118,y=b?Symbol.for("react.scope"):60119;
	function z(a){if("object"===typeof a&&null!==a){var u=a.$$typeof;switch(u){case c:switch(a=a.type,a){case l:case m:case e:case g:case f:case p:return a;default:switch(a=a&&a.$$typeof,a){case k:case n:case t:case r:case h:return a;default:return u}}case d:return u}}}function A(a){return z(a)===m}reactIs_production_min.AsyncMode=l;reactIs_production_min.ConcurrentMode=m;reactIs_production_min.ContextConsumer=k;reactIs_production_min.ContextProvider=h;reactIs_production_min.Element=c;reactIs_production_min.ForwardRef=n;reactIs_production_min.Fragment=e;reactIs_production_min.Lazy=t;reactIs_production_min.Memo=r;reactIs_production_min.Portal=d;
	reactIs_production_min.Profiler=g;reactIs_production_min.StrictMode=f;reactIs_production_min.Suspense=p;reactIs_production_min.isAsyncMode=function(a){return A(a)||z(a)===l};reactIs_production_min.isConcurrentMode=A;reactIs_production_min.isContextConsumer=function(a){return z(a)===k};reactIs_production_min.isContextProvider=function(a){return z(a)===h};reactIs_production_min.isElement=function(a){return "object"===typeof a&&null!==a&&a.$$typeof===c};reactIs_production_min.isForwardRef=function(a){return z(a)===n};reactIs_production_min.isFragment=function(a){return z(a)===e};reactIs_production_min.isLazy=function(a){return z(a)===t};
	reactIs_production_min.isMemo=function(a){return z(a)===r};reactIs_production_min.isPortal=function(a){return z(a)===d};reactIs_production_min.isProfiler=function(a){return z(a)===g};reactIs_production_min.isStrictMode=function(a){return z(a)===f};reactIs_production_min.isSuspense=function(a){return z(a)===p};
	reactIs_production_min.isValidElementType=function(a){return "string"===typeof a||"function"===typeof a||a===e||a===m||a===g||a===f||a===p||a===q||"object"===typeof a&&null!==a&&(a.$$typeof===t||a.$$typeof===r||a.$$typeof===h||a.$$typeof===k||a.$$typeof===n||a.$$typeof===w||a.$$typeof===x||a.$$typeof===y||a.$$typeof===v)};reactIs_production_min.typeOf=z;
	return reactIs_production_min;
}

var reactIs_development = {};

/** @license React v16.13.1
 * react-is.development.js
 *
 * Copyright (c) Facebook, Inc. and its affiliates.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

var hasRequiredReactIs_development;

function requireReactIs_development () {
	if (hasRequiredReactIs_development) return reactIs_development;
	hasRequiredReactIs_development = 1;



	if (process.env.NODE_ENV !== "production") {
	  (function() {

	// The Symbol used to tag the ReactElement-like types. If there is no native Symbol
	// nor polyfill, then a plain number is used for performance.
	var hasSymbol = typeof Symbol === 'function' && Symbol.for;
	var REACT_ELEMENT_TYPE = hasSymbol ? Symbol.for('react.element') : 0xeac7;
	var REACT_PORTAL_TYPE = hasSymbol ? Symbol.for('react.portal') : 0xeaca;
	var REACT_FRAGMENT_TYPE = hasSymbol ? Symbol.for('react.fragment') : 0xeacb;
	var REACT_STRICT_MODE_TYPE = hasSymbol ? Symbol.for('react.strict_mode') : 0xeacc;
	var REACT_PROFILER_TYPE = hasSymbol ? Symbol.for('react.profiler') : 0xead2;
	var REACT_PROVIDER_TYPE = hasSymbol ? Symbol.for('react.provider') : 0xeacd;
	var REACT_CONTEXT_TYPE = hasSymbol ? Symbol.for('react.context') : 0xeace; // TODO: We don't use AsyncMode or ConcurrentMode anymore. They were temporary
	// (unstable) APIs that have been removed. Can we remove the symbols?

	var REACT_ASYNC_MODE_TYPE = hasSymbol ? Symbol.for('react.async_mode') : 0xeacf;
	var REACT_CONCURRENT_MODE_TYPE = hasSymbol ? Symbol.for('react.concurrent_mode') : 0xeacf;
	var REACT_FORWARD_REF_TYPE = hasSymbol ? Symbol.for('react.forward_ref') : 0xead0;
	var REACT_SUSPENSE_TYPE = hasSymbol ? Symbol.for('react.suspense') : 0xead1;
	var REACT_SUSPENSE_LIST_TYPE = hasSymbol ? Symbol.for('react.suspense_list') : 0xead8;
	var REACT_MEMO_TYPE = hasSymbol ? Symbol.for('react.memo') : 0xead3;
	var REACT_LAZY_TYPE = hasSymbol ? Symbol.for('react.lazy') : 0xead4;
	var REACT_BLOCK_TYPE = hasSymbol ? Symbol.for('react.block') : 0xead9;
	var REACT_FUNDAMENTAL_TYPE = hasSymbol ? Symbol.for('react.fundamental') : 0xead5;
	var REACT_RESPONDER_TYPE = hasSymbol ? Symbol.for('react.responder') : 0xead6;
	var REACT_SCOPE_TYPE = hasSymbol ? Symbol.for('react.scope') : 0xead7;

	function isValidElementType(type) {
	  return typeof type === 'string' || typeof type === 'function' || // Note: its typeof might be other than 'symbol' or 'number' if it's a polyfill.
	  type === REACT_FRAGMENT_TYPE || type === REACT_CONCURRENT_MODE_TYPE || type === REACT_PROFILER_TYPE || type === REACT_STRICT_MODE_TYPE || type === REACT_SUSPENSE_TYPE || type === REACT_SUSPENSE_LIST_TYPE || typeof type === 'object' && type !== null && (type.$$typeof === REACT_LAZY_TYPE || type.$$typeof === REACT_MEMO_TYPE || type.$$typeof === REACT_PROVIDER_TYPE || type.$$typeof === REACT_CONTEXT_TYPE || type.$$typeof === REACT_FORWARD_REF_TYPE || type.$$typeof === REACT_FUNDAMENTAL_TYPE || type.$$typeof === REACT_RESPONDER_TYPE || type.$$typeof === REACT_SCOPE_TYPE || type.$$typeof === REACT_BLOCK_TYPE);
	}

	function typeOf(object) {
	  if (typeof object === 'object' && object !== null) {
	    var $$typeof = object.$$typeof;

	    switch ($$typeof) {
	      case REACT_ELEMENT_TYPE:
	        var type = object.type;

	        switch (type) {
	          case REACT_ASYNC_MODE_TYPE:
	          case REACT_CONCURRENT_MODE_TYPE:
	          case REACT_FRAGMENT_TYPE:
	          case REACT_PROFILER_TYPE:
	          case REACT_STRICT_MODE_TYPE:
	          case REACT_SUSPENSE_TYPE:
	            return type;

	          default:
	            var $$typeofType = type && type.$$typeof;

	            switch ($$typeofType) {
	              case REACT_CONTEXT_TYPE:
	              case REACT_FORWARD_REF_TYPE:
	              case REACT_LAZY_TYPE:
	              case REACT_MEMO_TYPE:
	              case REACT_PROVIDER_TYPE:
	                return $$typeofType;

	              default:
	                return $$typeof;
	            }

	        }

	      case REACT_PORTAL_TYPE:
	        return $$typeof;
	    }
	  }

	  return undefined;
	} // AsyncMode is deprecated along with isAsyncMode

	var AsyncMode = REACT_ASYNC_MODE_TYPE;
	var ConcurrentMode = REACT_CONCURRENT_MODE_TYPE;
	var ContextConsumer = REACT_CONTEXT_TYPE;
	var ContextProvider = REACT_PROVIDER_TYPE;
	var Element = REACT_ELEMENT_TYPE;
	var ForwardRef = REACT_FORWARD_REF_TYPE;
	var Fragment = REACT_FRAGMENT_TYPE;
	var Lazy = REACT_LAZY_TYPE;
	var Memo = REACT_MEMO_TYPE;
	var Portal = REACT_PORTAL_TYPE;
	var Profiler = REACT_PROFILER_TYPE;
	var StrictMode = REACT_STRICT_MODE_TYPE;
	var Suspense = REACT_SUSPENSE_TYPE;
	var hasWarnedAboutDeprecatedIsAsyncMode = false; // AsyncMode should be deprecated

	function isAsyncMode(object) {
	  {
	    if (!hasWarnedAboutDeprecatedIsAsyncMode) {
	      hasWarnedAboutDeprecatedIsAsyncMode = true; // Using console['warn'] to evade Babel and ESLint

	      console['warn']('The ReactIs.isAsyncMode() alias has been deprecated, ' + 'and will be removed in React 17+. Update your code to use ' + 'ReactIs.isConcurrentMode() instead. It has the exact same API.');
	    }
	  }

	  return isConcurrentMode(object) || typeOf(object) === REACT_ASYNC_MODE_TYPE;
	}
	function isConcurrentMode(object) {
	  return typeOf(object) === REACT_CONCURRENT_MODE_TYPE;
	}
	function isContextConsumer(object) {
	  return typeOf(object) === REACT_CONTEXT_TYPE;
	}
	function isContextProvider(object) {
	  return typeOf(object) === REACT_PROVIDER_TYPE;
	}
	function isElement(object) {
	  return typeof object === 'object' && object !== null && object.$$typeof === REACT_ELEMENT_TYPE;
	}
	function isForwardRef(object) {
	  return typeOf(object) === REACT_FORWARD_REF_TYPE;
	}
	function isFragment(object) {
	  return typeOf(object) === REACT_FRAGMENT_TYPE;
	}
	function isLazy(object) {
	  return typeOf(object) === REACT_LAZY_TYPE;
	}
	function isMemo(object) {
	  return typeOf(object) === REACT_MEMO_TYPE;
	}
	function isPortal(object) {
	  return typeOf(object) === REACT_PORTAL_TYPE;
	}
	function isProfiler(object) {
	  return typeOf(object) === REACT_PROFILER_TYPE;
	}
	function isStrictMode(object) {
	  return typeOf(object) === REACT_STRICT_MODE_TYPE;
	}
	function isSuspense(object) {
	  return typeOf(object) === REACT_SUSPENSE_TYPE;
	}

	reactIs_development.AsyncMode = AsyncMode;
	reactIs_development.ConcurrentMode = ConcurrentMode;
	reactIs_development.ContextConsumer = ContextConsumer;
	reactIs_development.ContextProvider = ContextProvider;
	reactIs_development.Element = Element;
	reactIs_development.ForwardRef = ForwardRef;
	reactIs_development.Fragment = Fragment;
	reactIs_development.Lazy = Lazy;
	reactIs_development.Memo = Memo;
	reactIs_development.Portal = Portal;
	reactIs_development.Profiler = Profiler;
	reactIs_development.StrictMode = StrictMode;
	reactIs_development.Suspense = Suspense;
	reactIs_development.isAsyncMode = isAsyncMode;
	reactIs_development.isConcurrentMode = isConcurrentMode;
	reactIs_development.isContextConsumer = isContextConsumer;
	reactIs_development.isContextProvider = isContextProvider;
	reactIs_development.isElement = isElement;
	reactIs_development.isForwardRef = isForwardRef;
	reactIs_development.isFragment = isFragment;
	reactIs_development.isLazy = isLazy;
	reactIs_development.isMemo = isMemo;
	reactIs_development.isPortal = isPortal;
	reactIs_development.isProfiler = isProfiler;
	reactIs_development.isStrictMode = isStrictMode;
	reactIs_development.isSuspense = isSuspense;
	reactIs_development.isValidElementType = isValidElementType;
	reactIs_development.typeOf = typeOf;
	  })();
	}
	return reactIs_development;
}

var hasRequiredReactIs;

function requireReactIs () {
	if (hasRequiredReactIs) return reactIs.exports;
	hasRequiredReactIs = 1;

	if (process.env.NODE_ENV === 'production') {
	  reactIs.exports = requireReactIs_production_min();
	} else {
	  reactIs.exports = requireReactIs_development();
	}
	return reactIs.exports;
}

/*
object-assign
(c) Sindre Sorhus
@license MIT
*/

var objectAssign;
var hasRequiredObjectAssign;

function requireObjectAssign () {
	if (hasRequiredObjectAssign) return objectAssign;
	hasRequiredObjectAssign = 1;
	/* eslint-disable no-unused-vars */
	var getOwnPropertySymbols = Object.getOwnPropertySymbols;
	var hasOwnProperty = Object.prototype.hasOwnProperty;
	var propIsEnumerable = Object.prototype.propertyIsEnumerable;

	function toObject(val) {
		if (val === null || val === undefined) {
			throw new TypeError('Object.assign cannot be called with null or undefined');
		}

		return Object(val);
	}

	function shouldUseNative() {
		try {
			if (!Object.assign) {
				return false;
			}

			// Detect buggy property enumeration order in older V8 versions.

			// https://bugs.chromium.org/p/v8/issues/detail?id=4118
			var test1 = new String('abc');  // eslint-disable-line no-new-wrappers
			test1[5] = 'de';
			if (Object.getOwnPropertyNames(test1)[0] === '5') {
				return false;
			}

			// https://bugs.chromium.org/p/v8/issues/detail?id=3056
			var test2 = {};
			for (var i = 0; i < 10; i++) {
				test2['_' + String.fromCharCode(i)] = i;
			}
			var order2 = Object.getOwnPropertyNames(test2).map(function (n) {
				return test2[n];
			});
			if (order2.join('') !== '0123456789') {
				return false;
			}

			// https://bugs.chromium.org/p/v8/issues/detail?id=3056
			var test3 = {};
			'abcdefghijklmnopqrst'.split('').forEach(function (letter) {
				test3[letter] = letter;
			});
			if (Object.keys(Object.assign({}, test3)).join('') !==
					'abcdefghijklmnopqrst') {
				return false;
			}

			return true;
		} catch (err) {
			// We don't expect any of the above to throw, but better to be safe.
			return false;
		}
	}

	objectAssign = shouldUseNative() ? Object.assign : function (target, source) {
		var from;
		var to = toObject(target);
		var symbols;

		for (var s = 1; s < arguments.length; s++) {
			from = Object(arguments[s]);

			for (var key in from) {
				if (hasOwnProperty.call(from, key)) {
					to[key] = from[key];
				}
			}

			if (getOwnPropertySymbols) {
				symbols = getOwnPropertySymbols(from);
				for (var i = 0; i < symbols.length; i++) {
					if (propIsEnumerable.call(from, symbols[i])) {
						to[symbols[i]] = from[symbols[i]];
					}
				}
			}
		}

		return to;
	};
	return objectAssign;
}

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

var ReactPropTypesSecret_1;
var hasRequiredReactPropTypesSecret;

function requireReactPropTypesSecret () {
	if (hasRequiredReactPropTypesSecret) return ReactPropTypesSecret_1;
	hasRequiredReactPropTypesSecret = 1;

	var ReactPropTypesSecret = 'SECRET_DO_NOT_PASS_THIS_OR_YOU_WILL_BE_FIRED';

	ReactPropTypesSecret_1 = ReactPropTypesSecret;
	return ReactPropTypesSecret_1;
}

var has;
var hasRequiredHas;

function requireHas () {
	if (hasRequiredHas) return has;
	hasRequiredHas = 1;
	has = Function.call.bind(Object.prototype.hasOwnProperty);
	return has;
}

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

var checkPropTypes_1;
var hasRequiredCheckPropTypes;

function requireCheckPropTypes () {
	if (hasRequiredCheckPropTypes) return checkPropTypes_1;
	hasRequiredCheckPropTypes = 1;

	var printWarning = function() {};

	if (process.env.NODE_ENV !== 'production') {
	  var ReactPropTypesSecret = requireReactPropTypesSecret();
	  var loggedTypeFailures = {};
	  var has = requireHas();

	  printWarning = function(text) {
	    var message = 'Warning: ' + text;
	    if (typeof console !== 'undefined') {
	      console.error(message);
	    }
	    try {
	      // --- Welcome to debugging React ---
	      // This error was thrown as a convenience so that you can use this stack
	      // to find the callsite that caused this warning to fire.
	      throw new Error(message);
	    } catch (x) { /**/ }
	  };
	}

	/**
	 * Assert that the values match with the type specs.
	 * Error messages are memorized and will only be shown once.
	 *
	 * @param {object} typeSpecs Map of name to a ReactPropType
	 * @param {object} values Runtime values that need to be type-checked
	 * @param {string} location e.g. "prop", "context", "child context"
	 * @param {string} componentName Name of the component for error messages.
	 * @param {?Function} getStack Returns the component stack.
	 * @private
	 */
	function checkPropTypes(typeSpecs, values, location, componentName, getStack) {
	  if (process.env.NODE_ENV !== 'production') {
	    for (var typeSpecName in typeSpecs) {
	      if (has(typeSpecs, typeSpecName)) {
	        var error;
	        // Prop type validation may throw. In case they do, we don't want to
	        // fail the render phase where it didn't fail before. So we log it.
	        // After these have been cleaned up, we'll let them throw.
	        try {
	          // This is intentionally an invariant that gets caught. It's the same
	          // behavior as without this statement except with a better message.
	          if (typeof typeSpecs[typeSpecName] !== 'function') {
	            var err = Error(
	              (componentName || 'React class') + ': ' + location + ' type `' + typeSpecName + '` is invalid; ' +
	              'it must be a function, usually from the `prop-types` package, but received `' + typeof typeSpecs[typeSpecName] + '`.' +
	              'This often happens because of typos such as `PropTypes.function` instead of `PropTypes.func`.'
	            );
	            err.name = 'Invariant Violation';
	            throw err;
	          }
	          error = typeSpecs[typeSpecName](values, typeSpecName, componentName, location, null, ReactPropTypesSecret);
	        } catch (ex) {
	          error = ex;
	        }
	        if (error && !(error instanceof Error)) {
	          printWarning(
	            (componentName || 'React class') + ': type specification of ' +
	            location + ' `' + typeSpecName + '` is invalid; the type checker ' +
	            'function must return `null` or an `Error` but returned a ' + typeof error + '. ' +
	            'You may have forgotten to pass an argument to the type checker ' +
	            'creator (arrayOf, instanceOf, objectOf, oneOf, oneOfType, and ' +
	            'shape all require an argument).'
	          );
	        }
	        if (error instanceof Error && !(error.message in loggedTypeFailures)) {
	          // Only monitor this failure once because there tends to be a lot of the
	          // same error.
	          loggedTypeFailures[error.message] = true;

	          var stack = getStack ? getStack() : '';

	          printWarning(
	            'Failed ' + location + ' type: ' + error.message + (stack != null ? stack : '')
	          );
	        }
	      }
	    }
	  }
	}

	/**
	 * Resets warning cache when testing.
	 *
	 * @private
	 */
	checkPropTypes.resetWarningCache = function() {
	  if (process.env.NODE_ENV !== 'production') {
	    loggedTypeFailures = {};
	  }
	};

	checkPropTypes_1 = checkPropTypes;
	return checkPropTypes_1;
}

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

var factoryWithTypeCheckers;
var hasRequiredFactoryWithTypeCheckers;

function requireFactoryWithTypeCheckers () {
	if (hasRequiredFactoryWithTypeCheckers) return factoryWithTypeCheckers;
	hasRequiredFactoryWithTypeCheckers = 1;

	var ReactIs = requireReactIs();
	var assign = requireObjectAssign();

	var ReactPropTypesSecret = requireReactPropTypesSecret();
	var has = requireHas();
	var checkPropTypes = requireCheckPropTypes();

	var printWarning = function() {};

	if (process.env.NODE_ENV !== 'production') {
	  printWarning = function(text) {
	    var message = 'Warning: ' + text;
	    if (typeof console !== 'undefined') {
	      console.error(message);
	    }
	    try {
	      // --- Welcome to debugging React ---
	      // This error was thrown as a convenience so that you can use this stack
	      // to find the callsite that caused this warning to fire.
	      throw new Error(message);
	    } catch (x) {}
	  };
	}

	function emptyFunctionThatReturnsNull() {
	  return null;
	}

	factoryWithTypeCheckers = function(isValidElement, throwOnDirectAccess) {
	  /* global Symbol */
	  var ITERATOR_SYMBOL = typeof Symbol === 'function' && Symbol.iterator;
	  var FAUX_ITERATOR_SYMBOL = '@@iterator'; // Before Symbol spec.

	  /**
	   * Returns the iterator method function contained on the iterable object.
	   *
	   * Be sure to invoke the function with the iterable as context:
	   *
	   *     var iteratorFn = getIteratorFn(myIterable);
	   *     if (iteratorFn) {
	   *       var iterator = iteratorFn.call(myIterable);
	   *       ...
	   *     }
	   *
	   * @param {?object} maybeIterable
	   * @return {?function}
	   */
	  function getIteratorFn(maybeIterable) {
	    var iteratorFn = maybeIterable && (ITERATOR_SYMBOL && maybeIterable[ITERATOR_SYMBOL] || maybeIterable[FAUX_ITERATOR_SYMBOL]);
	    if (typeof iteratorFn === 'function') {
	      return iteratorFn;
	    }
	  }

	  /**
	   * Collection of methods that allow declaration and validation of props that are
	   * supplied to React components. Example usage:
	   *
	   *   var Props = require('ReactPropTypes');
	   *   var MyArticle = React.createClass({
	   *     propTypes: {
	   *       // An optional string prop named "description".
	   *       description: Props.string,
	   *
	   *       // A required enum prop named "category".
	   *       category: Props.oneOf(['News','Photos']).isRequired,
	   *
	   *       // A prop named "dialog" that requires an instance of Dialog.
	   *       dialog: Props.instanceOf(Dialog).isRequired
	   *     },
	   *     render: function() { ... }
	   *   });
	   *
	   * A more formal specification of how these methods are used:
	   *
	   *   type := array|bool|func|object|number|string|oneOf([...])|instanceOf(...)
	   *   decl := ReactPropTypes.{type}(.isRequired)?
	   *
	   * Each and every declaration produces a function with the same signature. This
	   * allows the creation of custom validation functions. For example:
	   *
	   *  var MyLink = React.createClass({
	   *    propTypes: {
	   *      // An optional string or URI prop named "href".
	   *      href: function(props, propName, componentName) {
	   *        var propValue = props[propName];
	   *        if (propValue != null && typeof propValue !== 'string' &&
	   *            !(propValue instanceof URI)) {
	   *          return new Error(
	   *            'Expected a string or an URI for ' + propName + ' in ' +
	   *            componentName
	   *          );
	   *        }
	   *      }
	   *    },
	   *    render: function() {...}
	   *  });
	   *
	   * @internal
	   */

	  var ANONYMOUS = '<<anonymous>>';

	  // Important!
	  // Keep this list in sync with production version in `./factoryWithThrowingShims.js`.
	  var ReactPropTypes = {
	    array: createPrimitiveTypeChecker('array'),
	    bigint: createPrimitiveTypeChecker('bigint'),
	    bool: createPrimitiveTypeChecker('boolean'),
	    func: createPrimitiveTypeChecker('function'),
	    number: createPrimitiveTypeChecker('number'),
	    object: createPrimitiveTypeChecker('object'),
	    string: createPrimitiveTypeChecker('string'),
	    symbol: createPrimitiveTypeChecker('symbol'),

	    any: createAnyTypeChecker(),
	    arrayOf: createArrayOfTypeChecker,
	    element: createElementTypeChecker(),
	    elementType: createElementTypeTypeChecker(),
	    instanceOf: createInstanceTypeChecker,
	    node: createNodeChecker(),
	    objectOf: createObjectOfTypeChecker,
	    oneOf: createEnumTypeChecker,
	    oneOfType: createUnionTypeChecker,
	    shape: createShapeTypeChecker,
	    exact: createStrictShapeTypeChecker,
	  };

	  /**
	   * inlined Object.is polyfill to avoid requiring consumers ship their own
	   * https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Object/is
	   */
	  /*eslint-disable no-self-compare*/
	  function is(x, y) {
	    // SameValue algorithm
	    if (x === y) {
	      // Steps 1-5, 7-10
	      // Steps 6.b-6.e: +0 != -0
	      return x !== 0 || 1 / x === 1 / y;
	    } else {
	      // Step 6.a: NaN == NaN
	      return x !== x && y !== y;
	    }
	  }
	  /*eslint-enable no-self-compare*/

	  /**
	   * We use an Error-like object for backward compatibility as people may call
	   * PropTypes directly and inspect their output. However, we don't use real
	   * Errors anymore. We don't inspect their stack anyway, and creating them
	   * is prohibitively expensive if they are created too often, such as what
	   * happens in oneOfType() for any type before the one that matched.
	   */
	  function PropTypeError(message, data) {
	    this.message = message;
	    this.data = data && typeof data === 'object' ? data: {};
	    this.stack = '';
	  }
	  // Make `instanceof Error` still work for returned errors.
	  PropTypeError.prototype = Error.prototype;

	  function createChainableTypeChecker(validate) {
	    if (process.env.NODE_ENV !== 'production') {
	      var manualPropTypeCallCache = {};
	      var manualPropTypeWarningCount = 0;
	    }
	    function checkType(isRequired, props, propName, componentName, location, propFullName, secret) {
	      componentName = componentName || ANONYMOUS;
	      propFullName = propFullName || propName;

	      if (secret !== ReactPropTypesSecret) {
	        if (throwOnDirectAccess) {
	          // New behavior only for users of `prop-types` package
	          var err = new Error(
	            'Calling PropTypes validators directly is not supported by the `prop-types` package. ' +
	            'Use `PropTypes.checkPropTypes()` to call them. ' +
	            'Read more at http://fb.me/use-check-prop-types'
	          );
	          err.name = 'Invariant Violation';
	          throw err;
	        } else if (process.env.NODE_ENV !== 'production' && typeof console !== 'undefined') {
	          // Old behavior for people using React.PropTypes
	          var cacheKey = componentName + ':' + propName;
	          if (
	            !manualPropTypeCallCache[cacheKey] &&
	            // Avoid spamming the console because they are often not actionable except for lib authors
	            manualPropTypeWarningCount < 3
	          ) {
	            printWarning(
	              'You are manually calling a React.PropTypes validation ' +
	              'function for the `' + propFullName + '` prop on `' + componentName + '`. This is deprecated ' +
	              'and will throw in the standalone `prop-types` package. ' +
	              'You may be seeing this warning due to a third-party PropTypes ' +
	              'library. See https://fb.me/react-warning-dont-call-proptypes ' + 'for details.'
	            );
	            manualPropTypeCallCache[cacheKey] = true;
	            manualPropTypeWarningCount++;
	          }
	        }
	      }
	      if (props[propName] == null) {
	        if (isRequired) {
	          if (props[propName] === null) {
	            return new PropTypeError('The ' + location + ' `' + propFullName + '` is marked as required ' + ('in `' + componentName + '`, but its value is `null`.'));
	          }
	          return new PropTypeError('The ' + location + ' `' + propFullName + '` is marked as required in ' + ('`' + componentName + '`, but its value is `undefined`.'));
	        }
	        return null;
	      } else {
	        return validate(props, propName, componentName, location, propFullName);
	      }
	    }

	    var chainedCheckType = checkType.bind(null, false);
	    chainedCheckType.isRequired = checkType.bind(null, true);

	    return chainedCheckType;
	  }

	  function createPrimitiveTypeChecker(expectedType) {
	    function validate(props, propName, componentName, location, propFullName, secret) {
	      var propValue = props[propName];
	      var propType = getPropType(propValue);
	      if (propType !== expectedType) {
	        // `propValue` being instance of, say, date/regexp, pass the 'object'
	        // check, but we can offer a more precise error message here rather than
	        // 'of type `object`'.
	        var preciseType = getPreciseType(propValue);

	        return new PropTypeError(
	          'Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + preciseType + '` supplied to `' + componentName + '`, expected ') + ('`' + expectedType + '`.'),
	          {expectedType: expectedType}
	        );
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createAnyTypeChecker() {
	    return createChainableTypeChecker(emptyFunctionThatReturnsNull);
	  }

	  function createArrayOfTypeChecker(typeChecker) {
	    function validate(props, propName, componentName, location, propFullName) {
	      if (typeof typeChecker !== 'function') {
	        return new PropTypeError('Property `' + propFullName + '` of component `' + componentName + '` has invalid PropType notation inside arrayOf.');
	      }
	      var propValue = props[propName];
	      if (!Array.isArray(propValue)) {
	        var propType = getPropType(propValue);
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected an array.'));
	      }
	      for (var i = 0; i < propValue.length; i++) {
	        var error = typeChecker(propValue, i, componentName, location, propFullName + '[' + i + ']', ReactPropTypesSecret);
	        if (error instanceof Error) {
	          return error;
	        }
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createElementTypeChecker() {
	    function validate(props, propName, componentName, location, propFullName) {
	      var propValue = props[propName];
	      if (!isValidElement(propValue)) {
	        var propType = getPropType(propValue);
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected a single ReactElement.'));
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createElementTypeTypeChecker() {
	    function validate(props, propName, componentName, location, propFullName) {
	      var propValue = props[propName];
	      if (!ReactIs.isValidElementType(propValue)) {
	        var propType = getPropType(propValue);
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected a single ReactElement type.'));
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createInstanceTypeChecker(expectedClass) {
	    function validate(props, propName, componentName, location, propFullName) {
	      if (!(props[propName] instanceof expectedClass)) {
	        var expectedClassName = expectedClass.name || ANONYMOUS;
	        var actualClassName = getClassName(props[propName]);
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + actualClassName + '` supplied to `' + componentName + '`, expected ') + ('instance of `' + expectedClassName + '`.'));
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createEnumTypeChecker(expectedValues) {
	    if (!Array.isArray(expectedValues)) {
	      if (process.env.NODE_ENV !== 'production') {
	        if (arguments.length > 1) {
	          printWarning(
	            'Invalid arguments supplied to oneOf, expected an array, got ' + arguments.length + ' arguments. ' +
	            'A common mistake is to write oneOf(x, y, z) instead of oneOf([x, y, z]).'
	          );
	        } else {
	          printWarning('Invalid argument supplied to oneOf, expected an array.');
	        }
	      }
	      return emptyFunctionThatReturnsNull;
	    }

	    function validate(props, propName, componentName, location, propFullName) {
	      var propValue = props[propName];
	      for (var i = 0; i < expectedValues.length; i++) {
	        if (is(propValue, expectedValues[i])) {
	          return null;
	        }
	      }

	      var valuesString = JSON.stringify(expectedValues, function replacer(key, value) {
	        var type = getPreciseType(value);
	        if (type === 'symbol') {
	          return String(value);
	        }
	        return value;
	      });
	      return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of value `' + String(propValue) + '` ' + ('supplied to `' + componentName + '`, expected one of ' + valuesString + '.'));
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createObjectOfTypeChecker(typeChecker) {
	    function validate(props, propName, componentName, location, propFullName) {
	      if (typeof typeChecker !== 'function') {
	        return new PropTypeError('Property `' + propFullName + '` of component `' + componentName + '` has invalid PropType notation inside objectOf.');
	      }
	      var propValue = props[propName];
	      var propType = getPropType(propValue);
	      if (propType !== 'object') {
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type ' + ('`' + propType + '` supplied to `' + componentName + '`, expected an object.'));
	      }
	      for (var key in propValue) {
	        if (has(propValue, key)) {
	          var error = typeChecker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret);
	          if (error instanceof Error) {
	            return error;
	          }
	        }
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createUnionTypeChecker(arrayOfTypeCheckers) {
	    if (!Array.isArray(arrayOfTypeCheckers)) {
	      process.env.NODE_ENV !== 'production' ? printWarning('Invalid argument supplied to oneOfType, expected an instance of array.') : void 0;
	      return emptyFunctionThatReturnsNull;
	    }

	    for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
	      var checker = arrayOfTypeCheckers[i];
	      if (typeof checker !== 'function') {
	        printWarning(
	          'Invalid argument supplied to oneOfType. Expected an array of check functions, but ' +
	          'received ' + getPostfixForTypeWarning(checker) + ' at index ' + i + '.'
	        );
	        return emptyFunctionThatReturnsNull;
	      }
	    }

	    function validate(props, propName, componentName, location, propFullName) {
	      var expectedTypes = [];
	      for (var i = 0; i < arrayOfTypeCheckers.length; i++) {
	        var checker = arrayOfTypeCheckers[i];
	        var checkerResult = checker(props, propName, componentName, location, propFullName, ReactPropTypesSecret);
	        if (checkerResult == null) {
	          return null;
	        }
	        if (checkerResult.data && has(checkerResult.data, 'expectedType')) {
	          expectedTypes.push(checkerResult.data.expectedType);
	        }
	      }
	      var expectedTypesMessage = (expectedTypes.length > 0) ? ', expected one of type [' + expectedTypes.join(', ') + ']': '';
	      return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` supplied to ' + ('`' + componentName + '`' + expectedTypesMessage + '.'));
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createNodeChecker() {
	    function validate(props, propName, componentName, location, propFullName) {
	      if (!isNode(props[propName])) {
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` supplied to ' + ('`' + componentName + '`, expected a ReactNode.'));
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function invalidValidatorError(componentName, location, propFullName, key, type) {
	    return new PropTypeError(
	      (componentName || 'React class') + ': ' + location + ' type `' + propFullName + '.' + key + '` is invalid; ' +
	      'it must be a function, usually from the `prop-types` package, but received `' + type + '`.'
	    );
	  }

	  function createShapeTypeChecker(shapeTypes) {
	    function validate(props, propName, componentName, location, propFullName) {
	      var propValue = props[propName];
	      var propType = getPropType(propValue);
	      if (propType !== 'object') {
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type `' + propType + '` ' + ('supplied to `' + componentName + '`, expected `object`.'));
	      }
	      for (var key in shapeTypes) {
	        var checker = shapeTypes[key];
	        if (typeof checker !== 'function') {
	          return invalidValidatorError(componentName, location, propFullName, key, getPreciseType(checker));
	        }
	        var error = checker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret);
	        if (error) {
	          return error;
	        }
	      }
	      return null;
	    }
	    return createChainableTypeChecker(validate);
	  }

	  function createStrictShapeTypeChecker(shapeTypes) {
	    function validate(props, propName, componentName, location, propFullName) {
	      var propValue = props[propName];
	      var propType = getPropType(propValue);
	      if (propType !== 'object') {
	        return new PropTypeError('Invalid ' + location + ' `' + propFullName + '` of type `' + propType + '` ' + ('supplied to `' + componentName + '`, expected `object`.'));
	      }
	      // We need to check all keys in case some are required but missing from props.
	      var allKeys = assign({}, props[propName], shapeTypes);
	      for (var key in allKeys) {
	        var checker = shapeTypes[key];
	        if (has(shapeTypes, key) && typeof checker !== 'function') {
	          return invalidValidatorError(componentName, location, propFullName, key, getPreciseType(checker));
	        }
	        if (!checker) {
	          return new PropTypeError(
	            'Invalid ' + location + ' `' + propFullName + '` key `' + key + '` supplied to `' + componentName + '`.' +
	            '\nBad object: ' + JSON.stringify(props[propName], null, '  ') +
	            '\nValid keys: ' + JSON.stringify(Object.keys(shapeTypes), null, '  ')
	          );
	        }
	        var error = checker(propValue, key, componentName, location, propFullName + '.' + key, ReactPropTypesSecret);
	        if (error) {
	          return error;
	        }
	      }
	      return null;
	    }

	    return createChainableTypeChecker(validate);
	  }

	  function isNode(propValue) {
	    switch (typeof propValue) {
	      case 'number':
	      case 'string':
	      case 'undefined':
	        return true;
	      case 'boolean':
	        return !propValue;
	      case 'object':
	        if (Array.isArray(propValue)) {
	          return propValue.every(isNode);
	        }
	        if (propValue === null || isValidElement(propValue)) {
	          return true;
	        }

	        var iteratorFn = getIteratorFn(propValue);
	        if (iteratorFn) {
	          var iterator = iteratorFn.call(propValue);
	          var step;
	          if (iteratorFn !== propValue.entries) {
	            while (!(step = iterator.next()).done) {
	              if (!isNode(step.value)) {
	                return false;
	              }
	            }
	          } else {
	            // Iterator will provide entry [k,v] tuples rather than values.
	            while (!(step = iterator.next()).done) {
	              var entry = step.value;
	              if (entry) {
	                if (!isNode(entry[1])) {
	                  return false;
	                }
	              }
	            }
	          }
	        } else {
	          return false;
	        }

	        return true;
	      default:
	        return false;
	    }
	  }

	  function isSymbol(propType, propValue) {
	    // Native Symbol.
	    if (propType === 'symbol') {
	      return true;
	    }

	    // falsy value can't be a Symbol
	    if (!propValue) {
	      return false;
	    }

	    // 19.4.3.5 Symbol.prototype[@@toStringTag] === 'Symbol'
	    if (propValue['@@toStringTag'] === 'Symbol') {
	      return true;
	    }

	    // Fallback for non-spec compliant Symbols which are polyfilled.
	    if (typeof Symbol === 'function' && propValue instanceof Symbol) {
	      return true;
	    }

	    return false;
	  }

	  // Equivalent of `typeof` but with special handling for array and regexp.
	  function getPropType(propValue) {
	    var propType = typeof propValue;
	    if (Array.isArray(propValue)) {
	      return 'array';
	    }
	    if (propValue instanceof RegExp) {
	      // Old webkits (at least until Android 4.0) return 'function' rather than
	      // 'object' for typeof a RegExp. We'll normalize this here so that /bla/
	      // passes PropTypes.object.
	      return 'object';
	    }
	    if (isSymbol(propType, propValue)) {
	      return 'symbol';
	    }
	    return propType;
	  }

	  // This handles more types than `getPropType`. Only used for error messages.
	  // See `createPrimitiveTypeChecker`.
	  function getPreciseType(propValue) {
	    if (typeof propValue === 'undefined' || propValue === null) {
	      return '' + propValue;
	    }
	    var propType = getPropType(propValue);
	    if (propType === 'object') {
	      if (propValue instanceof Date) {
	        return 'date';
	      } else if (propValue instanceof RegExp) {
	        return 'regexp';
	      }
	    }
	    return propType;
	  }

	  // Returns a string that is postfixed to a warning about an invalid type.
	  // For example, "undefined" or "of type array"
	  function getPostfixForTypeWarning(value) {
	    var type = getPreciseType(value);
	    switch (type) {
	      case 'array':
	      case 'object':
	        return 'an ' + type;
	      case 'boolean':
	      case 'date':
	      case 'regexp':
	        return 'a ' + type;
	      default:
	        return type;
	    }
	  }

	  // Returns class name of the object, if any.
	  function getClassName(propValue) {
	    if (!propValue.constructor || !propValue.constructor.name) {
	      return ANONYMOUS;
	    }
	    return propValue.constructor.name;
	  }

	  ReactPropTypes.checkPropTypes = checkPropTypes;
	  ReactPropTypes.resetWarningCache = checkPropTypes.resetWarningCache;
	  ReactPropTypes.PropTypes = ReactPropTypes;

	  return ReactPropTypes;
	};
	return factoryWithTypeCheckers;
}

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

var factoryWithThrowingShims;
var hasRequiredFactoryWithThrowingShims;

function requireFactoryWithThrowingShims () {
	if (hasRequiredFactoryWithThrowingShims) return factoryWithThrowingShims;
	hasRequiredFactoryWithThrowingShims = 1;

	var ReactPropTypesSecret = requireReactPropTypesSecret();

	function emptyFunction() {}
	function emptyFunctionWithReset() {}
	emptyFunctionWithReset.resetWarningCache = emptyFunction;

	factoryWithThrowingShims = function() {
	  function shim(props, propName, componentName, location, propFullName, secret) {
	    if (secret === ReactPropTypesSecret) {
	      // It is still safe when called from React.
	      return;
	    }
	    var err = new Error(
	      'Calling PropTypes validators directly is not supported by the `prop-types` package. ' +
	      'Use PropTypes.checkPropTypes() to call them. ' +
	      'Read more at http://fb.me/use-check-prop-types'
	    );
	    err.name = 'Invariant Violation';
	    throw err;
	  }	  shim.isRequired = shim;
	  function getShim() {
	    return shim;
	  }	  // Important!
	  // Keep this list in sync with production version in `./factoryWithTypeCheckers.js`.
	  var ReactPropTypes = {
	    array: shim,
	    bigint: shim,
	    bool: shim,
	    func: shim,
	    number: shim,
	    object: shim,
	    string: shim,
	    symbol: shim,

	    any: shim,
	    arrayOf: getShim,
	    element: shim,
	    elementType: shim,
	    instanceOf: getShim,
	    node: shim,
	    objectOf: getShim,
	    oneOf: getShim,
	    oneOfType: getShim,
	    shape: getShim,
	    exact: getShim,

	    checkPropTypes: emptyFunctionWithReset,
	    resetWarningCache: emptyFunction
	  };

	  ReactPropTypes.PropTypes = ReactPropTypes;

	  return ReactPropTypes;
	};
	return factoryWithThrowingShims;
}

/**
 * Copyright (c) 2013-present, Facebook, Inc.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 */

if (process.env.NODE_ENV !== 'production') {
  var ReactIs = requireReactIs();

  // By explicitly using `prop-types` you are opting into new development behavior.
  // http://fb.me/prop-types-in-prod
  var throwOnDirectAccess = true;
  propTypes.exports = requireFactoryWithTypeCheckers()(ReactIs.isElement, throwOnDirectAccess);
} else {
  // By explicitly using `prop-types` you are opting into new production behavior.
  // http://fb.me/prop-types-in-prod
  propTypes.exports = requireFactoryWithThrowingShims()();
}

var propTypesExports = propTypes.exports;
var PropTypes = /*@__PURE__*/getDefaultExportFromCjs(propTypesExports);

var classnames = {exports: {}};

/*!
	Copyright (c) 2018 Jed Watson.
	Licensed under the MIT License (MIT), see
	http://jedwatson.github.io/classnames
*/

(function (module) {
	/* global define */

	(function () {

		var hasOwn = {}.hasOwnProperty;

		function classNames() {
			var classes = [];

			for (var i = 0; i < arguments.length; i++) {
				var arg = arguments[i];
				if (!arg) continue;

				var argType = typeof arg;

				if (argType === 'string' || argType === 'number') {
					classes.push(arg);
				} else if (Array.isArray(arg)) {
					if (arg.length) {
						var inner = classNames.apply(null, arg);
						if (inner) {
							classes.push(inner);
						}
					}
				} else if (argType === 'object') {
					if (arg.toString !== Object.prototype.toString && !arg.toString.toString().includes('[native code]')) {
						classes.push(arg.toString());
						continue;
					}

					for (var key in arg) {
						if (hasOwn.call(arg, key) && arg[key]) {
							classes.push(key);
						}
					}
				}
			}

			return classes.join(' ');
		}

		if (module.exports) {
			classNames.default = classNames;
			module.exports = classNames;
		} else {
			window.classNames = classNames;
		}
	}()); 
} (classnames));

var classnamesExports = classnames.exports;
var classNames = /*@__PURE__*/getDefaultExportFromCjs(classnamesExports);

var toCamelCase = function (str) {
    return str
        .replace(/([-_][a-z0-9])/gi, function ($1) {
        return $1.toUpperCase();
    })
        .replace(/-/gi, '');
};
var CIcon = React$1.forwardRef(function (_a, ref) {
    var _b;
    var className = _a.className, content = _a.content, customClassName = _a.customClassName, height = _a.height, icon = _a.icon, name = _a.name, size = _a.size, title = _a.title, use = _a.use, width = _a.width, rest = __rest(_a, ["className", "content", "customClassName", "height", "icon", "name", "size", "title", "use", "width"]);
    var _c = React$1.useState(0), change = _c[0], setChange = _c[1];
    var _icon = icon || content || name;
    if (content) {
        process &&
            process.env &&
            process.env.NODE_ENV === 'development' &&
            console.warn('[CIcon] The `content` property is deprecated and will be removed in v3, please use `icon={...}` instead of.');
    }
    if (name) {
        process &&
            process.env &&
            process.env.NODE_ENV === 'development' &&
            console.warn('[CIcon] The `name` property is deprecated and will be removed in v3, please use `icon="..."` instead of.');
    }
    React$1.useMemo(function () { return setChange(change + 1); }, [_icon, JSON.stringify(_icon)]);
    var titleCode = title ? "<title>".concat(title, "</title>") : '';
    var code = React$1.useMemo(function () {
        var iconName = _icon && typeof _icon === 'string' && _icon.includes('-') ? toCamelCase(_icon) : _icon;
        if (Array.isArray(_icon)) {
            return _icon;
        }
        if (typeof _icon === 'string' && React$1['icons']) {
            return React$1['icons'][iconName];
        }
    }, [change]);
    var iconCode = React$1.useMemo(function () {
        return Array.isArray(code) ? code[1] || code[0] : code;
    }, [change]);
    var scale = (function () {
        return Array.isArray(code) && code.length > 1 ? code[0] : '64 64';
    })();
    var viewBox = (function () {
        return rest['viewBox'] || "0 0 ".concat(scale);
    })();
    var _className = customClassName
        ? classNames(customClassName)
        : classNames('icon', (_b = {},
            _b["icon-".concat(size)] = size,
            _b["icon-custom-size"] = height || width,
            _b), className);
    return (React$1.createElement(React$1.Fragment, null,
        use ? (React$1.createElement("svg", __assign({ xmlns: "http://www.w3.org/2000/svg", className: _className }, (height && { height: height }), (width && { width: width }), { role: "img", "aria-hidden": "true" }, rest, { ref: ref }),
            React$1.createElement("use", { href: use }))) : (React$1.createElement("svg", __assign({ xmlns: "http://www.w3.org/2000/svg", viewBox: viewBox, className: _className }, (height && { height: height }), (width && { width: width }), { role: "img", "aria-hidden": "true", dangerouslySetInnerHTML: { __html: titleCode + iconCode } }, rest, { ref: ref }))),
        title && React$1.createElement("span", { className: "visually-hidden" }, title)));
});
CIcon.propTypes = {
    className: PropTypes.string,
    content: PropTypes.oneOfType([PropTypes.array, PropTypes.string]),
    customClassName: PropTypes.string,
    height: PropTypes.number,
    icon: PropTypes.oneOfType([PropTypes.array, PropTypes.string]),
    name: PropTypes.string,
    size: PropTypes.oneOf([
        'custom',
        'custom-size',
        'sm',
        'lg',
        'xl',
        'xxl',
        '3xl',
        '4xl',
        '5xl',
        '6xl',
        '7xl',
        '8xl',
        '9xl',
    ]),
    title: PropTypes.any,
    use: PropTypes.any,
    width: PropTypes.number,
};
CIcon.displayName = 'CIcon';

var CSmartPagination = React$1.forwardRef(function (_a, ref) {
    var className = _a.className, _b = _a.activePage, activePage = _b === void 0 ? 1 : _b, _c = _a.align, align = _c === void 0 ? 'start' : _c, _d = _a.arrows, arrows = _d === void 0 ? true : _d, _e = _a.dots, dots = _e === void 0 ? true : _e, _f = _a.doubleArrows, doubleArrows = _f === void 0 ? true : _f, _g = _a.firstButton, firstButton = _g === void 0 ? React$1.createElement(React$1.Fragment, null, "\u00AB") : _g, _h = _a.lastButton, lastButton = _h === void 0 ? React$1.createElement(React$1.Fragment, null, "\u00BB") : _h, _j = _a.limit, limit = _j === void 0 ? 5 : _j, _k = _a.nextButton, nextButton = _k === void 0 ? React$1.createElement(React$1.Fragment, null, "\u203A") : _k, onActivePageChange = _a.onActivePageChange, pages = _a.pages, _l = _a.previousButton, previousButton = _l === void 0 ? React$1.createElement(React$1.Fragment, null, "\u2039") : _l, size = _a.size, rest = __rest$1(_a, ["className", "activePage", "align", "arrows", "dots", "doubleArrows", "firstButton", "lastButton", "limit", "nextButton", "onActivePageChange", "pages", "previousButton", "size"]);
    var showDots = (function () {
        return dots && limit > 4 && limit < pages;
    })();
    var maxPrevItems = (function () {
        return Math.floor((limit - 1) / 2);
    })();
    var maxNextItems = (function () {
        return Math.ceil((limit - 1) / 2);
    })();
    var beforeDots = (function () {
        return showDots && activePage > maxPrevItems + 1;
    })();
    var afterDots = (function () {
        return showDots && activePage < pages - maxNextItems;
    })();
    var computedLimit = (function () {
        return limit - (afterDots ? 1 : 0) - (beforeDots ? 1 : 0);
    })();
    var range = (function () {
        return activePage + maxNextItems;
    })();
    var lastItem = (function () {
        return range >= pages ? pages : range - (afterDots ? 1 : 0);
    })();
    var itemsAmount = (function () {
        return pages < computedLimit ? pages : computedLimit;
    })();
    var items = (function () {
        return activePage - maxPrevItems <= 1
            ? Array.from({
                length: itemsAmount,
            }, function (_v, i) { return i + 1; })
            : Array.from({
                length: itemsAmount,
            }, function (_v, i) {
                return lastItem - i;
            }).reverse();
    })();
    var setPage = function (number) {
        if (number !== activePage) {
            onActivePageChange && onActivePageChange(number);
        }
    };
    return (React$1.createElement(CPagination, __assign$1({ className: classNames$1("justify-content-".concat(align), className), "aria-label": "pagination", size: size }, rest, { ref: ref }),
        doubleArrows && (React$1.createElement(CPaginationItem, { onClick: function () { return setPage(1); }, "aria-label": "Go to first page", "aria-disabled": activePage === 1, disabled: activePage === 1 }, firstButton)),
        arrows && (React$1.createElement(CPaginationItem, { onClick: function () { return setPage(activePage - 1); }, "aria-label": "Go to previous page", "aria-disabled": activePage === 1, disabled: activePage === 1 }, previousButton)),
        beforeDots && (React$1.createElement(CPaginationItem, { role: "separator", disabled: true }, "\u2026")),
        items.map(function (i) {
            return (React$1.createElement(CPaginationItem, { onClick: function () { return setPage(i); }, "aria-label": activePage === i ? "Current page ".concat(i) : "Go to page ".concat(i), active: activePage === i, key: i }, i));
        }),
        afterDots && (React$1.createElement(CPaginationItem, { role: "separator", disabled: true }, "\u2026")),
        arrows && (React$1.createElement(CPaginationItem, { onClick: function () { return setPage(activePage + 1); }, "aria-label": "Go to next page", "aria-disabled": activePage === pages, disabled: activePage === pages }, nextButton)),
        doubleArrows && (React$1.createElement(CPaginationItem, { onClick: function () { return setPage(pages); }, "aria-label": "Go to last page", "aria-disabled": activePage === pages, disabled: activePage === pages }, lastButton))));
});
CSmartPagination.propTypes = {
    className: PropTypes$1.oneOfType([PropTypes$1.string]),
    activePage: PropTypes$1.number,
    dots: PropTypes$1.bool,
    arrows: PropTypes$1.bool,
    doubleArrows: PropTypes$1.bool,
    firstButton: PropTypes$1.oneOfType([PropTypes$1.node, PropTypes$1.string]),
    previousButton: PropTypes$1.oneOfType([PropTypes$1.node, PropTypes$1.string]),
    nextButton: PropTypes$1.oneOfType([PropTypes$1.node, PropTypes$1.string]),
    lastButton: PropTypes$1.oneOfType([PropTypes$1.node, PropTypes$1.string]),
    size: PropTypes$1.oneOf(['sm', 'lg']),
    align: PropTypes$1.oneOf(['start', 'center', 'end']),
    limit: PropTypes$1.number,
    pages: PropTypes$1.number.isRequired,
    onActivePageChange: PropTypes$1.func,
};
CSmartPagination.displayName = 'CSmartPagination';

var CTableHead = React$1.forwardRef(function (_a, ref) {
    var _b;
    var children = _a.children, className = _a.className, color = _a.color, rest = __rest$1(_a, ["children", "className", "color"]);
    return (React$1.createElement("thead", __assign$1({ className: classNames$1((_b = {},
            _b["table-".concat(color)] = color,
            _b), className) || undefined }, rest, { ref: ref }), children));
});
CTableHead.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    color: colorPropType,
};
CTableHead.displayName = 'CTableHead';

var CTableHeaderCell = React$1.forwardRef(function (_a, ref) {
    var _b;
    var children = _a.children, className = _a.className, color = _a.color, rest = __rest$1(_a, ["children", "className", "color"]);
    return (React$1.createElement("th", __assign$1({ className: classNames$1((_b = {},
            _b["table-".concat(color)] = color,
            _b), className) || undefined }, rest, { ref: ref }), children));
});
CTableHeaderCell.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    color: colorPropType,
};
CTableHeaderCell.displayName = 'CTableHeaderCell';

var CTableBody = React$1.forwardRef(function (_a, ref) {
    var _b;
    var children = _a.children, className = _a.className, color = _a.color, rest = __rest$1(_a, ["children", "className", "color"]);
    return (React$1.createElement("tbody", __assign$1({ className: classNames$1((_b = {},
            _b["table-".concat(color)] = color,
            _b), className) || undefined }, rest, { ref: ref }), children));
});
CTableBody.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    color: colorPropType,
};
CTableBody.displayName = 'CTableBody';

var CTableDataCell = React$1.forwardRef(function (_a, ref) {
    var _b;
    var children = _a.children, active = _a.active, align = _a.align, className = _a.className, color = _a.color, rest = __rest$1(_a, ["children", "active", "align", "className", "color"]);
    var Component = rest.scope ? 'th' : 'td';
    return (React$1.createElement(Component, __assign$1({ className: classNames$1((_b = {},
            _b["align-".concat(align)] = align,
            _b['table-active'] = active,
            _b["table-".concat(color)] = color,
            _b), className) || undefined }, rest, { ref: ref }), children));
});
CTableDataCell.propTypes = {
    active: PropTypes$1.bool,
    align: PropTypes$1.oneOf(['bottom', 'middle', 'top']),
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    color: colorPropType,
};
CTableDataCell.displayName = 'CTableDataCell';

var CTableRow = React$1.forwardRef(function (_a, ref) {
    var _b;
    var children = _a.children, active = _a.active, align = _a.align, className = _a.className, color = _a.color, rest = __rest$1(_a, ["children", "active", "align", "className", "color"]);
    return (React$1.createElement("tr", __assign$1({ className: classNames$1((_b = {},
            _b["align-".concat(align)] = align,
            _b['table-active'] = active,
            _b["table-".concat(color)] = color,
            _b), className) || undefined }, rest, { ref: ref }), children));
});
CTableRow.propTypes = {
    active: PropTypes$1.bool,
    align: PropTypes$1.oneOf(['bottom', 'middle', 'top']),
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    color: colorPropType,
};
CTableRow.displayName = 'CTableRow';

var CTableFoot = React$1.forwardRef(function (_a, ref) {
    var _b;
    var children = _a.children, className = _a.className, color = _a.color, rest = __rest$1(_a, ["children", "className", "color"]);
    return (React$1.createElement("tfoot", __assign$1({ className: classNames$1((_b = {},
            _b["table-".concat(color)] = color,
            _b), className) || undefined }, rest, { ref: ref }), children));
});
CTableFoot.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    color: colorPropType,
};
CTableFoot.displayName = 'CTableFoot';

var CTableCaption = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, props = __rest$1(_a, ["children"]);
    return (React$1.createElement("caption", __assign$1({}, props, { ref: ref }), children));
});
CTableCaption.propTypes = {
    children: PropTypes$1.node,
};
CTableCaption.displayName = 'CTableCaption';

var CTableResponsiveWrapper = function (_a) {
    var children = _a.children, responsive = _a.responsive, rest = __rest$1(_a, ["children", "responsive"]);
    return responsive ? (React$1.createElement("div", __assign$1({ className: typeof responsive === 'boolean' ? 'table-responsive' : "table-responsive-".concat(responsive) }, rest), children)) : (React$1.createElement(React$1.Fragment, null, children));
};
CTableResponsiveWrapper.propTypes = {
    children: PropTypes$1.node,
    responsive: PropTypes$1.oneOfType([
        PropTypes$1.bool,
        PropTypes$1.oneOf(['sm', 'md', 'lg', 'xl', 'xxl']),
    ]),
};
CTableResponsiveWrapper.displayName = 'CTableResponsiveWrapper';

var pretifyName$1 = function (name) {
    return name
        .replace(/[-_.]/g, ' ')
        .replace(/ +/g, ' ')
        .replace(/([a-z0-9])([A-Z])/g, '$1 $2')
        .split(' ')
        .map(function (word) { return word.charAt(0).toUpperCase() + word.slice(1); })
        .join(' ');
};
var getColumnLabel$1 = function (column) { var _a; return typeof column === 'object' ? (_a = column.label) !== null && _a !== void 0 ? _a : pretifyName$1(column.key) : pretifyName$1(column); };
var getColumnNames$1 = function (columns, items) {
    return columns
        ? columns.map(function (column) {
            return typeof column === 'object' ? column.key : column;
        })
        : items && getColumnNamesFromItems$1(items);
};
var getColumnNamesFromItems$1 = function (items) {
    return Object.keys(items[0] || {}).filter(function (el) { return el.charAt(0) !== '_'; });
};

var CTable = React$1.forwardRef(function (_a, ref) {
    var _b;
    var children = _a.children, align = _a.align, borderColor = _a.borderColor, bordered = _a.bordered, borderless = _a.borderless, caption = _a.caption, captionTop = _a.captionTop, className = _a.className, color = _a.color, columns = _a.columns, footer = _a.footer, hover = _a.hover, items = _a.items, responsive = _a.responsive, small = _a.small, striped = _a.striped, stripedColumns = _a.stripedColumns, tableFootProps = _a.tableFootProps, tableHeadProps = _a.tableHeadProps, rest = __rest$1(_a, ["children", "align", "borderColor", "bordered", "borderless", "caption", "captionTop", "className", "color", "columns", "footer", "hover", "items", "responsive", "small", "striped", "stripedColumns", "tableFootProps", "tableHeadProps"]);
    var columnNames = React$1.useMemo(function () { return getColumnNames$1(columns, items); }, [columns, items]);
    return (React$1.createElement(CTableResponsiveWrapper, { responsive: responsive },
        React$1.createElement("table", __assign$1({ className: classNames$1('table', (_b = {},
                _b["align-".concat(align)] = align,
                _b["border-".concat(borderColor)] = borderColor,
                _b["caption-top"] = captionTop || caption === 'top',
                _b['table-bordered'] = bordered,
                _b['table-borderless'] = borderless,
                _b["table-".concat(color)] = color,
                _b['table-hover'] = hover,
                _b['table-sm'] = small,
                _b['table-striped'] = striped,
                _b['table-striped-columns'] = stripedColumns,
                _b), className) }, rest, { ref: ref }),
            ((caption && caption !== 'top') || captionTop) && (React$1.createElement(CTableCaption, null, caption || captionTop)),
            columns && (React$1.createElement(CTableHead, __assign$1({}, tableHeadProps),
                React$1.createElement(CTableRow, null, columns.map(function (column, index) { return (React$1.createElement(CTableHeaderCell, __assign$1({}, (column._props && __assign$1({}, column._props)), (column._style && { style: __assign$1({}, column._style) }), { key: index }), getColumnLabel$1(column))); })))),
            items && (React$1.createElement(CTableBody, null, items.map(function (item, index) { return (React$1.createElement(CTableRow, __assign$1({}, (item._props && __assign$1({}, item._props)), { key: index }), columnNames &&
                columnNames.map(function (colName, index) {
                    // eslint-disable-next-line unicorn/no-negated-condition
                    return item[colName] !== undefined ? (React$1.createElement(CTableDataCell, __assign$1({}, (item._cellProps && __assign$1(__assign$1({}, (item._cellProps['all'] && __assign$1({}, item._cellProps['all']))), (item._cellProps[colName] && __assign$1({}, item._cellProps[colName])))), { key: index }), item[colName])) : null;
                }))); }))),
            children,
            footer && (React$1.createElement(CTableFoot, __assign$1({}, tableFootProps),
                React$1.createElement(CTableRow, null, footer.map(function (item, index) { return (React$1.createElement(CTableDataCell, __assign$1({}, (typeof item === 'object' && item._props && __assign$1({}, item._props)), { key: index }), typeof item === 'object' ? item.label : item)); })))))));
});
CTable.propTypes = {
    align: PropTypes$1.oneOf(['bottom', 'middle', 'top']),
    borderColor: PropTypes$1.string,
    bordered: PropTypes$1.bool,
    borderless: PropTypes$1.bool,
    caption: PropTypes$1.oneOfType([PropTypes$1.string, PropTypes$1.oneOf(['top'])]),
    captionTop: PropTypes$1.string,
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    color: colorPropType,
    columns: PropTypes$1.array,
    footer: PropTypes$1.array,
    hover: PropTypes$1.bool,
    items: PropTypes$1.array,
    responsive: PropTypes$1.oneOfType([
        PropTypes$1.bool,
        PropTypes$1.oneOf(['sm', 'md', 'lg', 'xl', 'xxl']),
    ]),
    small: PropTypes$1.bool,
    striped: PropTypes$1.bool,
    stripedColumns: PropTypes$1.bool,
    tableFootProps: PropTypes$1.shape(__assign$1({}, CTableFoot.propTypes)),
    tableHeadProps: PropTypes$1.shape(__assign$1({}, CTableHead.propTypes)),
};
CTable.displayName = 'CTable';

var filterColumns = function (items, columnFilter, columnFilterState, itemsDataColumns) {
    if (columnFilter && typeof columnFilter === 'object' && columnFilter.external) {
        return items;
    }
    Object.entries(columnFilterState).forEach(function (_a) {
        var key = _a[0], value = _a[1];
        if (value instanceof Function) {
            items = items.filter(function (item) { return value(item[key]); });
            return;
        }
        var columnFilter = String(value).toLowerCase();
        if (columnFilter && itemsDataColumns.includes(key)) {
            items = items.filter(function (item) {
                return String(item[key]).toLowerCase().includes(columnFilter);
            });
        }
    });
    return items;
};
var filterTable = function (items, tableFilter, tableFilterState, itemsDataColumns) {
    if (!tableFilterState ||
        (tableFilter && typeof tableFilter === 'object' && tableFilter.external)) {
        return items;
    }
    var filter = tableFilterState.toLowerCase();
    var valueContainFilter = function (val) { return String(val).toLowerCase().includes(filter); };
    items = items.filter(function (item) {
        return !!itemsDataColumns.find(function (key) { return valueContainFilter(item[key]); });
    });
    return items;
};
var getClickedColumnName = function (target, columnNames) {
    var closest = target.closest('tr');
    var children = closest ? Array.from(closest.children) : [];
    var clickedCell = children.filter(function (child) { return child.contains(target); })[0];
    return columnNames[children.indexOf(clickedCell)];
};
var getColumnKey = function (column) {
    return typeof column === 'object' ? column.key : column;
};
var getColumnLabel = function (column) {
    return typeof column === 'object'
        ? column.label !== undefined
            ? column.label
            : pretifyName(column.key)
        : pretifyName(column);
};
var getColumnNames = function (columns, items) {
    if (columns) {
        var _columns = [];
        for (var _i = 0, columns_1 = columns; _i < columns_1.length; _i++) {
            var column = columns_1[_i];
            if (typeof column === 'object' && column.children) {
                _columns.push.apply(_columns, getColumnNames(column.children, []));
                continue;
            }
            typeof column === 'object' ? _columns.push(column.key) : _columns.push(column);
        }
        return _columns;
    }
    return getColumnNamesFromItems(items);
};
var getColumns = function (_columns) {
    var columns = [];
    for (var _i = 0, _columns_1 = _columns; _i < _columns_1.length; _i++) {
        var column = _columns_1[_i];
        if (typeof column === 'object' && column.group && column.children) {
            columns.push.apply(columns, getColumns(column.children));
            continue;
        }
        if (typeof column === 'object' && column.children) {
            columns.push.apply(columns, getColumns(column.children));
        }
        columns.push(column);
    }
    return columns;
};
var countColumns = function (columns, counter) {
    if (counter === void 0) { counter = 0; }
    var _counter = counter;
    for (var _i = 0, columns_2 = columns; _i < columns_2.length; _i++) {
        var column = columns_2[_i];
        if (!column.children) {
            _counter++;
        }
        if (column.children) {
            _counter = countColumns(column.children, _counter);
        }
    }
    return _counter;
};
var getColumnGroups = function (columns) {
    var groups = [];
    var traverseColumns = function (column, deep, colSpan) {
        if (deep === void 0) { deep = 0; }
        var groups = [];
        if (column.children) {
            for (var _i = 0, _a = column.children; _i < _a.length; _i++) {
                var _column = _a[_i];
                if (!_column.group) ;
                groups.push.apply(groups, traverseColumns(_column, deep + 1));
            }
        }
        if (typeof column === 'object' && column.group) {
            var children = column.children, group = column.group, rest = __rest$1(column, ["children", "group"]);
            groups.push(__assign$1(__assign$1({ deep: deep, label: group }, (children && { colspan: countColumns(children) })), rest));
        }
        return groups;
    };
    if (columns) {
        for (var _i = 0, columns_3 = columns; _i < columns_3.length; _i++) {
            var column = columns_3[_i];
            if (typeof column === 'object' && column.group) {
                var objects = traverseColumns(column);
                if (objects) {
                    for (var _a = 0, objects_1 = objects; _a < objects_1.length; _a++) {
                        var object = objects_1[_a];
                        var deep = object.deep, rest = __rest$1(object, ["deep"]);
                        if (deep === undefined) {
                            continue;
                        }
                        for (var i = 0; i < deep; i++) {
                            if (groups[i]) {
                                continue;
                            }
                            groups.push([]);
                        }
                        if (groups[deep]) {
                            groups[deep].push(rest);
                        }
                        else {
                            groups.push([rest]);
                        }
                    }
                }
            }
        }
    }
    return groups;
};
var getColumnNamesFromItems = function (items) {
    return Object.keys(items[0] || {}).filter(function (el) { return el.charAt(0) !== '_'; });
};
var getColumnSorterState = function (key, sorterState) {
    if (sorterState && sorterState.column === key) {
        if (sorterState.state) {
            return sorterState.state;
        }
        return 0;
    }
    return 0;
};
var getColumnValues = function (items, key) {
    return items.map(function (item) { return item[key]; });
};
var getTableDataCellProps = function (item, colName) {
    var props = item._cellProps && __assign$1(__assign$1({}, (item._cellProps['all'] && __assign$1({}, item._cellProps['all']))), (item._cellProps[colName] && __assign$1({}, item._cellProps[colName])));
    return props;
};
var getTableHeaderCellProps = function (column) {
    if (typeof column === 'object' && column._props) {
        return column._props;
    }
    return {};
};
var getTableHeaderCellStyles = function (column, columnSorter) {
    var style = {};
    if (columnSorter &&
        (typeof column !== 'object' ||
            (typeof column === 'object' && (column.sorter === undefined || column.sorter)))) {
        style['cursor'] = 'pointer';
    }
    if (typeof column === 'object' && column._style) {
        return __assign$1(__assign$1({}, style), column._style);
    }
    return style;
};
var isSortable = function (i, columns, columnSorter, itemsDataColumns, columnNames) {
    var isDataColumn = itemsDataColumns.includes(columnNames[i]);
    var column;
    if (columns)
        column = columns[i];
    return (columnSorter &&
        (!columns ||
            typeof column !== 'object' ||
            (typeof column === 'object' && (column.sorter === undefined || column.sorter))) &&
        isDataColumn);
};
var pretifyName = function (name) {
    return name
        .replace(/[-_.]/g, ' ')
        .replace(/ +/g, ' ')
        .replace(/([a-z0-9])([A-Z])/g, '$1 $2')
        .split(' ')
        .map(function (word) { return word.charAt(0).toUpperCase() + word.slice(1); })
        .join(' ');
};
var sortItems = function (columnSorter, items, itemsDataColumns, sorterState) {
    var column = sorterState.column;
    if (!column ||
        !itemsDataColumns.includes(column) ||
        (columnSorter && typeof columnSorter === 'object' && columnSorter.external)) {
        return items;
    }
    var flip = sorterState.state === 'asc' ? 1 : sorterState.state === 'desc' ? -1 : 0;
    var sorted = items.slice().sort(function (item, item2) {
        var value = item[column];
        var value2 = item2[column];
        var a = typeof value === 'number' ? value : String(value).toLowerCase();
        var b = typeof value2 === 'number' ? value2 : String(value2).toLowerCase();
        return a > b ? 1 * flip : b > a ? -1 * flip : 0;
    });
    return sorted;
};

var CSmartTableBody = React$1.forwardRef(function (_a, ref) {
    var clickableRows = _a.clickableRows, columnNames = _a.columnNames, currentItems = _a.currentItems, firstItemOnActivePageIndex = _a.firstItemOnActivePageIndex, noItemsLabel = _a.noItemsLabel, onRowChecked = _a.onRowChecked, onRowClick = _a.onRowClick, scopedColumns = _a.scopedColumns, selectable = _a.selectable, selected = _a.selected, rest = __rest$1(_a, ["clickableRows", "columnNames", "currentItems", "firstItemOnActivePageIndex", "noItemsLabel", "onRowChecked", "onRowClick", "scopedColumns", "selectable", "selected"]);
    var colspan = selectable ? columnNames.length + 1 : columnNames.length;
    return (React$1.createElement(CTableBody, __assign$1({}, (clickableRows && {
        style: { cursor: 'pointer' },
    }), rest, { ref: ref }), currentItems.length > 0 ? (currentItems.map(function (item, trIndex) {
        return (React$1.createElement(React$1.Fragment, { key: trIndex },
            React$1.createElement(CTableRow, __assign$1({}, (item._props && __assign$1({}, item._props)), (clickableRows && { tabIndex: 0 }), { onClick: function (event) {
                    return onRowClick &&
                        onRowClick(item, trIndex + firstItemOnActivePageIndex, getClickedColumnName(event.target, columnNames), event);
                } }),
                selectable && (React$1.createElement(CTableDataCell, null,
                    React$1.createElement(CFormCheck, { checked: selected &&
                            isObjectInArray(selected, item, ['_cellProps', '_props', '_selected']), onChange: function (event) {
                            var _item = __assign$1({}, item);
                            delete _item['_cellProps'];
                            delete _item['_props'];
                            delete _item['_selected'];
                            onRowChecked && onRowChecked(_item, event.target.checked);
                        } }))),
                columnNames.map(function (colName, index) {
                    return ((scopedColumns &&
                        scopedColumns[colName] &&
                        React$1.cloneElement(scopedColumns[colName](item, trIndex + firstItemOnActivePageIndex), {
                            key: index,
                        })) ||
                        (item[colName] !== undefined && (React$1.createElement(CTableDataCell, __assign$1({}, getTableDataCellProps(item, colName), { key: index }), item[colName]))));
                })),
            scopedColumns && scopedColumns.details && (React$1.createElement(React$1.Fragment, null,
                React$1.createElement(CTableRow, null,
                    React$1.createElement(CTableDataCell, { colSpan: colspan, className: "p-0", style: { borderBottomWidth: 0 }, tabIndex: -1 })),
                React$1.createElement(CTableRow, { onClick: function (event) {
                        return onRowClick &&
                            onRowClick(item, trIndex + firstItemOnActivePageIndex, getClickedColumnName(event.target, columnNames), true);
                    }, className: "p-0", key: "details".concat(trIndex) },
                    React$1.createElement(CTableDataCell, { colSpan: colspan, className: "p-0", style: { border: 0 } }, scopedColumns.details(item, trIndex + firstItemOnActivePageIndex)))))));
    })) : (React$1.createElement(CTableRow, null,
        React$1.createElement(CTableDataCell, { colSpan: colspan }, noItemsLabel)))));
});
CSmartTableBody.propTypes = {
    clickableRows: PropTypes$1.bool,
    currentItems: PropTypes$1.array.isRequired,
    firstItemOnActivePageIndex: PropTypes$1.number.isRequired,
    noItemsLabel: PropTypes$1.oneOfType([PropTypes$1.string, PropTypes$1.node]),
    onRowChecked: PropTypes$1.func,
    onRowClick: PropTypes$1.func,
    columnNames: PropTypes$1.array.isRequired,
    scopedColumns: PropTypes$1.object,
    selectable: PropTypes$1.bool,
    selected: PropTypes$1.array,
};
CSmartTableBody.displayName = 'CSmartTableBody';

var CSmartTableHead = React$1.forwardRef(function (_a, ref) {
    var columnFilter = _a.columnFilter, columnFilterState = _a.columnFilterState, columnSorter = _a.columnSorter, _b = _a.component, Component = _b === void 0 ? CTableHead : _b, columns = _a.columns, handleOnCustomFilterChange = _a.handleOnCustomFilterChange, handleFilterOnChange = _a.handleFilterOnChange, handleFilterOnInput = _a.handleFilterOnInput, handleSelectAllChecked = _a.handleSelectAllChecked, handleSort = _a.handleSort, items = _a.items, selectable = _a.selectable, selectAll = _a.selectAll, selectedAll = _a.selectedAll, _c = _a.showGroups, showGroups = _c === void 0 ? true : _c, sorterState = _a.sorterState, sortingIcon = _a.sortingIcon, sortingIconAscending = _a.sortingIconAscending, sortingIconDescending = _a.sortingIconDescending, rest = __rest$1(_a, ["columnFilter", "columnFilterState", "columnSorter", "component", "columns", "handleOnCustomFilterChange", "handleFilterOnChange", "handleFilterOnInput", "handleSelectAllChecked", "handleSort", "items", "selectable", "selectAll", "selectedAll", "showGroups", "sorterState", "sortingIcon", "sortingIconAscending", "sortingIconDescending"]);
    var selectAllcheckboxRef = React$1.useRef(null);
    var _d = React$1.useState(false), refresh = _d[0], setRefresh = _d[1];
    var _columns = React$1.useMemo(function () { return getColumns(columns); }, [columns]);
    var groups = React$1.useMemo(function () { return getColumnGroups(columns); }, [columns]);
    React$1.useEffect(function () {
        if (columnFilterState && Object.keys(columnFilterState).length === 0) {
            setRefresh(true);
        }
    }, [columnFilterState]);
    React$1.useEffect(function () {
        setRefresh(true);
    }, [items]);
    React$1.useEffect(function () {
        if (setRefresh) {
            setRefresh(false);
        }
    }, [refresh]);
    var columnSorterIcon = function (column) {
        if (getColumnSorterState(getColumnKey(column), sorterState) === 0) {
            return React$1.createElement("span", { className: "opacity-25 float-end me-1" }, sortingIcon);
        }
        if (getColumnSorterState(getColumnKey(column), sorterState) === 'asc') {
            return React$1.createElement("span", { className: "float-end me-1" }, sortingIconAscending);
        }
        if (getColumnSorterState(getColumnKey(column), sorterState) === 'desc') {
            return React$1.createElement("span", { className: "float-end me-1" }, sortingIconDescending);
        }
        return;
    };
    return (React$1.createElement(Component, __assign$1({}, rest, { ref: ref }),
        showGroups &&
            groups &&
            groups.length > 0 &&
            groups.map(function (row, index) { return (React$1.createElement(CTableRow, { key: index },
                selectable && React$1.createElement(CTableHeaderCell, null),
                row.map(function (cell, index) { return (React$1.createElement(CTableHeaderCell, __assign$1({ colSpan: cell.colspan }, getTableHeaderCellProps(cell), { key: index }), cell.label)); }))); }),
        React$1.createElement(CTableRow, null,
            selectable && (React$1.createElement(CTableHeaderCell, null, selectAll && (React$1.createElement(CFormCheck, { checked: typeof selectedAll === 'boolean' ? selectedAll : false, indeterminate: selectedAll === 'indeterminate' ? true : false, onChange: function () { return handleSelectAllChecked && handleSelectAllChecked(); }, ref: selectAllcheckboxRef })))),
            _columns.map(function (column, index) {
                return (React$1.createElement(CTableHeaderCell, __assign$1({}, getTableHeaderCellProps(column), { onClick: function () { return handleSort && handleSort(getColumnKey(column), index); }, style: getTableHeaderCellStyles(column, columnSorter), key: index }),
                    React$1.createElement("div", { className: "d-inline" }, getColumnLabel(column)),
                    columnSorter &&
                        (typeof column === 'object'
                            ? (column.sorter === undefined
                                ? true
                                : column.sorter)
                            : true) &&
                        columnSorterIcon(column)));
            })),
        columnFilter && (React$1.createElement(CTableRow, null,
            selectable && React$1.createElement(CTableHeaderCell, null),
            _columns.map(function (column, index) {
                return (React$1.createElement(CTableHeaderCell, __assign$1({}, getTableHeaderCellProps(column), { key: index }), (typeof column === 'object'
                    ? (column.filter === undefined
                        ? true
                        : column.filter)
                    : true) ? (typeof column !== 'string' && typeof column.filter === 'function' ? (!refresh &&
                    column.filter(getColumnValues(items, getColumnKey(column)), function (value) {
                        return handleOnCustomFilterChange &&
                            handleOnCustomFilterChange(getColumnKey(column), value);
                    })) : (React$1.createElement(CFormInput, { size: "sm", onInput: function (event) {
                        return handleFilterOnInput &&
                            handleFilterOnInput(getColumnKey(column), event.target.value);
                    }, onChange: function (event) {
                        return handleFilterOnChange &&
                            handleFilterOnChange(getColumnKey(column), event.target.value);
                    }, value: columnFilterState && columnFilterState[getColumnKey(column)]
                        ? columnFilterState[getColumnKey(column)]
                        : '', "aria-label": "column name: '".concat(getColumnLabel(column), "' filter input") }))) : ('')));
            })))));
});
CSmartTableHead.propTypes = {
    columnFilter: PropTypes$1.oneOfType([PropTypes$1.bool, PropTypes$1.object]),
    columnFilterState: PropTypes$1.object,
    columnSorter: PropTypes$1.oneOfType([PropTypes$1.bool, PropTypes$1.object]),
    component: PropTypes$1.elementType,
    children: PropTypes$1.node,
    columns: PropTypes$1.arrayOf(PropTypes$1.oneOfType([PropTypes$1.any, PropTypes$1.string])).isRequired,
    handleFilterOnChange: PropTypes$1.func,
    handleFilterOnInput: PropTypes$1.func,
    handleSelectAllChecked: PropTypes$1.func,
    handleSort: PropTypes$1.func,
    selectable: PropTypes$1.bool,
    selectAll: PropTypes$1.oneOfType([PropTypes$1.bool, PropTypes$1.object]),
    selectedAll: PropTypes$1.oneOfType([PropTypes$1.bool, PropTypes$1.string]),
    sorterState: PropTypes$1.object,
    sortingIcon: PropTypes$1.node,
    sortingIconAscending: PropTypes$1.node,
    sortingIconDescending: PropTypes$1.node,
};
CSmartTableHead.displayName = 'CSmartTableHead';

var CSmartTable = React$1.forwardRef(function (_a, ref) {
    var _b = _a.activePage, activePage = _b === void 0 ? 1 : _b, cleaner = _a.cleaner, clickableRows = _a.clickableRows, columnFilter = _a.columnFilter, columnFilterValue = _a.columnFilterValue, // TODO: consider to use only columnFilter prop
    columns = _a.columns, columnSorter = _a.columnSorter, elementCover = _a.elementCover, footer = _a.footer, _c = _a.header, header = _c === void 0 ? true : _c, items = _a.items, itemsNumber = _a.itemsNumber, _d = _a.itemsPerPage, itemsPerPage = _d === void 0 ? 10 : _d, _e = _a.itemsPerPageLabel, itemsPerPageLabel = _e === void 0 ? 'Items per page:' : _e, _f = _a.itemsPerPageOptions, itemsPerPageOptions = _f === void 0 ? [5, 10, 20, 50] : _f, itemsPerPageSelect = _a.itemsPerPageSelect, loading = _a.loading, _g = _a.noItemsLabel, noItemsLabel = _g === void 0 ? 'No items found' : _g, onActivePageChange = _a.onActivePageChange, onColumnFilterChange = _a.onColumnFilterChange, onFilteredItemsChange = _a.onFilteredItemsChange, onItemsPerPageChange = _a.onItemsPerPageChange, onRowClick = _a.onRowClick, onSelectAll = _a.onSelectAll, onSelectedItemsChange = _a.onSelectedItemsChange, onSorterChange = _a.onSorterChange, onTableFilterChange = _a.onTableFilterChange, pagination = _a.pagination, paginationProps = _a.paginationProps, scopedColumns = _a.scopedColumns, selected = _a.selected, selectable = _a.selectable, _h = _a.selectAll, selectAll = _h === void 0 ? true : _h, sorterValue = _a.sorterValue, _j = _a.sortingIcon, sortingIcon = _j === void 0 ? React$1.createElement(CIcon, { width: 18, icon: cilSwapVertical, key: "csv" }) : _j, _k = _a.sortingIconAscending, sortingIconAscending = _k === void 0 ? React$1.createElement(CIcon, { width: 18, icon: cilArrowTop, key: "cat" }) : _k, _l = _a.sortingIconDescending, sortingIconDescending = _l === void 0 ? React$1.createElement(CIcon, { width: 18, icon: cilArrowBottom, key: "cab" }) : _l, tableBodyProps = _a.tableBodyProps, tableFootProps = _a.tableFootProps, tableFilter = _a.tableFilter, _m = _a.tableFilterLabel, tableFilterLabel = _m === void 0 ? 'Filter:' : _m, _o = _a.tableFilterPlaceholder, tableFilterPlaceholder = _o === void 0 ? 'type string...' : _o, tableFilterValue = _a.tableFilterValue, // TODO: consider to use only tableFilter prop
    tableHeadProps = _a.tableHeadProps, tableProps = _a.tableProps, rest = __rest$1(_a, ["activePage", "cleaner", "clickableRows", "columnFilter", "columnFilterValue", "columns", "columnSorter", "elementCover", "footer", "header", "items", "itemsNumber", "itemsPerPage", "itemsPerPageLabel", "itemsPerPageOptions", "itemsPerPageSelect", "loading", "noItemsLabel", "onActivePageChange", "onColumnFilterChange", "onFilteredItemsChange", "onItemsPerPageChange", "onRowClick", "onSelectAll", "onSelectedItemsChange", "onSorterChange", "onTableFilterChange", "pagination", "paginationProps", "scopedColumns", "selected", "selectable", "selectAll", "sorterValue", "sortingIcon", "sortingIconAscending", "sortingIconDescending", "tableBodyProps", "tableFootProps", "tableFilter", "tableFilterLabel", "tableFilterPlaceholder", "tableFilterValue", "tableHeadProps", "tableProps"]);
    var mountedRef = React$1.useRef(false);
    var _p = React$1.useState(activePage), _activePage = _p[0], setActivePage = _p[1];
    var _q = React$1.useState([]), _items = _q[0], setItems = _q[1];
    var _r = React$1.useState(itemsNumber), _itemsNumber = _r[0], setItemsNumber = _r[1];
    var _s = React$1.useState(itemsPerPage), _itemsPerPage = _s[0], setItemsPerPage = _s[1];
    var _t = React$1.useState([]), _selected = _t[0], setSelected = _t[1];
    var _u = React$1.useState({}), columnFilterState = _u[0], setColumnFilterState = _u[1];
    var _v = React$1.useState(), selectedAll = _v[0], setSelectedAll = _v[1];
    var _w = React$1.useState({}), sorterState = _w[0], setSorterState = _w[1];
    var _x = React$1.useState(tableFilterValue !== null && tableFilterValue !== void 0 ? tableFilterValue : ''), tableFilterState = _x[0], setTableFilterState = _x[1];
    React$1.useEffect(function () {
        setActivePage(activePage);
    }, [activePage]);
    React$1.useEffect(function () {
        if (items && items.length < _itemsPerPage * _activePage - _itemsPerPage) {
            setActivePage(1);
        }
        var selected = [];
        items &&
            items.forEach(function (item) {
                if (item._selected) {
                    var _item = __assign$1({}, item);
                    delete _item['_cellProps'];
                    delete _item['_props'];
                    delete _item['_selected'];
                    selected.push(_item);
                }
            });
        if (selected.length > 0) {
            setSelected(__spreadArray(__spreadArray([], _selected, true), selected, true));
        }
        if (Array.isArray(items)) {
            setItems(items);
            // eslint-disable-next-line unicorn/explicit-length-check
            setItemsNumber(itemsNumber || items.length);
        }
    }, [JSON.stringify(items)]);
    React$1.useEffect(function () {
        Array.isArray(selected) && setSelected(selected);
    }, [JSON.stringify(selected)]);
    React$1.useEffect(function () {
        itemsNumber && setItemsNumber(itemsNumber);
    }, [itemsNumber]);
    React$1.useEffect(function () {
        columnFilterValue && setColumnFilterState(columnFilterValue);
    }, [JSON.stringify(columnFilterValue)]);
    React$1.useEffect(function () {
        setSorterState(__assign$1({}, sorterValue));
    }, [JSON.stringify(sorterValue)]);
    React$1.useEffect(function () { return setItemsPerPage(itemsPerPage); }, [itemsPerPage]);
    React$1.useEffect(function () {
        mountedRef.current && onActivePageChange && onActivePageChange(_activePage);
    }, [_activePage]);
    React$1.useEffect(function () {
        mountedRef.current && onItemsPerPageChange && onItemsPerPageChange(_itemsPerPage);
        itemsPerPage !== _itemsPerPage && setActivePage(1); // TODO: set proper page after _itemsPerPage update
    }, [_itemsPerPage]);
    React$1.useEffect(function () {
        mountedRef.current && sorterState && onSorterChange && onSorterChange(sorterState);
    }, [JSON.stringify(sorterState)]);
    React$1.useEffect(function () {
        mountedRef.current && onColumnFilterChange && onColumnFilterChange(columnFilterState);
    }, [columnFilterState]);
    React$1.useEffect(function () {
        mountedRef.current && onTableFilterChange && onTableFilterChange(tableFilterState);
    }, [tableFilterState]);
    React$1.useEffect(function () {
        if (selectable) {
            onSelectedItemsChange && onSelectedItemsChange(_selected);
            if (_selected.length === _itemsNumber) {
                setSelectedAll(true);
                return;
            }
            if (_selected.length === 0) {
                setSelectedAll(false);
                return;
            }
            if (_selected.length > 0 && _selected.length !== _itemsNumber) {
                setSelectedAll('indeterminate');
            }
        }
    }, [JSON.stringify(_selected), _itemsNumber]);
    var columnNames = React$1.useMemo(function () { return getColumnNames(columns, _items); }, [columns, _items]);
    var itemsDataColumns = React$1.useMemo(function () { return columnNames.filter(function (name) { return getColumnNamesFromItems(_items).includes(name); }); }, [columnNames, _items]);
    var filteredColumns = React$1.useMemo(function () { return filterColumns(_items, columnFilter, columnFilterState, itemsDataColumns); }, [columnFilterState, JSON.stringify(_items)]);
    var filteredTable = React$1.useMemo(function () { return filterTable(filteredColumns, tableFilter, tableFilterState, itemsDataColumns); }, [tableFilterState, JSON.stringify(tableFilterValue), JSON.stringify(filteredColumns)]);
    var sortedItems = React$1.useMemo(function () { return sortItems(columnSorter, filteredTable, itemsDataColumns, sorterState); }, [
        JSON.stringify(filteredTable),
        JSON.stringify(sorterState),
        JSON.stringify(columnSorter),
        JSON.stringify(filteredColumns),
        JSON.stringify(_items),
    ]);
    var numberOfPages = _itemsPerPage ? Math.ceil(sortedItems.length / _itemsPerPage) : 1;
    var firstItemOnActivePageIndex = _activePage ? (_activePage - 1) * _itemsPerPage : 0;
    var currentItems = _activePage
        ? sortedItems.slice(firstItemOnActivePageIndex, firstItemOnActivePageIndex + _itemsPerPage)
        : sortedItems;
    React$1.useEffect(function () {
        mountedRef.current && onFilteredItemsChange && onFilteredItemsChange(sortedItems);
    }, [JSON.stringify(sortedItems)]);
    var handleClean = function () {
        setTableFilterState('');
        setColumnFilterState({});
        setSorterState({});
    };
    var handleColumnFilterChange = function (colName, value, type) {
        var _a;
        var isLazy = columnFilter && typeof columnFilter === 'object' && columnFilter.lazy === true;
        if ((isLazy && type === 'input') || (!isLazy && type === 'change')) {
            return;
        }
        var newState = __assign$1(__assign$1({}, columnFilterState), (_a = {}, _a["".concat(colName)] = value, _a));
        setActivePage(1);
        setColumnFilterState(newState);
    };
    var handleItemsPerPageChange = function (event) {
        if (typeof itemsPerPageSelect !== 'object' ||
            (typeof itemsPerPageSelect === 'object' && !itemsPerPageSelect.external)) {
            setItemsPerPage(Number(event.target.value));
        }
    };
    var handleRowChecked = function (item, value) {
        if (value && !isObjectInArray(_selected, item, ['_cellProps', '_props', '_selected'])) {
            setSelected(__spreadArray(__spreadArray([], _selected, true), [item], false));
            return;
        }
        setSelected(_selected.filter(function (_item) { return !isObjectInArray([_item], item, ['_cellProps', '_props', '_selected']); }));
    };
    var handleSelectAllChecked = function () {
        if (selectedAll === true) {
            setSelected([]);
            return;
        }
        onSelectAll && onSelectAll();
        if (selectAll && typeof selectAll === 'object' && selectAll.external) {
            return;
        }
        var selected = _items.map(function (item) {
            return __assign$1({}, item);
        });
        setSelected(selected.map(function (item) {
            delete item['_cellProps'];
            delete item['_props'];
            delete item['_selected'];
            return item;
        }));
    };
    var handleSorterChange = function (column, index) {
        if (!isSortable(index, columns, columnSorter, itemsDataColumns, columnNames)) {
            return;
        }
        //if column changed or sort was descending change asc to true
        var state = sorterState !== null && sorterState !== void 0 ? sorterState : { column: '', state: '' };
        if (state.column === column) {
            if (state.state === 0) {
                state.state = 'asc';
            }
            else if (state.state === 'asc') {
                state.state = 'desc';
            }
            else {
                state.state = typeof columnSorter === 'object' && !columnSorter.resetable ? 'asc' : 0;
            }
        }
        else {
            state.column = column;
            state.state = 'asc';
        }
        setSorterState(__assign$1({}, state));
    };
    var handleTableFilterChange = function (value, type) {
        var isLazy = tableFilter && typeof tableFilter === 'object' && tableFilter.lazy === true;
        if ((isLazy && type === 'input') || (!isLazy && type === 'change')) {
            return;
        }
        setActivePage(1);
        setTableFilterState(value);
    };
    React$1.useEffect(function () {
        mountedRef.current = true;
    }, []);
    return (React$1.createElement(React$1.Fragment, null,
        React$1.createElement("div", __assign$1({}, rest, { ref: ref }), (itemsPerPageSelect || tableFilter || cleaner) && (React$1.createElement("div", { className: "row my-2 mx-0" }, (tableFilter || cleaner) && (React$1.createElement(React$1.Fragment, null,
            React$1.createElement("div", { className: "col-auto p-0" }, tableFilter && (React$1.createElement("div", { className: "row mb-2" },
                React$1.createElement(CFormLabel, { className: "col-sm-auto col-form-label" }, tableFilterLabel),
                React$1.createElement("div", { className: "col-sm-auto" },
                    React$1.createElement(CFormInput, { onInput: function (e) {
                            handleTableFilterChange(e.target.value, 'input');
                        }, onChange: function (e) {
                            handleTableFilterChange(e.target.value, 'change');
                        }, placeholder: tableFilterPlaceholder, value: tableFilterState || '' }))))),
            React$1.createElement("div", { className: "col-auto p-0" }, cleaner && (React$1.createElement("button", __assign$1({ type: "button", className: "btn btn-transparent" }, (!(tableFilterState ||
                (sorterState === null || sorterState === void 0 ? void 0 : sorterState.column) ||
                Object.values(columnFilterState).join('')) && {
                disabled: true,
                tabIndex: -1,
            }), { onClick: function () { return handleClean(); }, onKeyDown: function (event) {
                    if (event.key === 'Enter')
                        handleClean();
                } }),
                React$1.createElement(CIcon, { width: 18, icon: cilFilterX }))))))))),
        React$1.createElement("div", { className: "position-relative" },
            React$1.createElement(CTable, __assign$1({}, tableProps),
                header && (React$1.createElement(CSmartTableHead, __assign$1({}, tableHeadProps, { columnFilter: columnFilter, columnFilterState: columnFilterState, columns: columns !== null && columns !== void 0 ? columns : columnNames, columnSorter: columnSorter, items: _items, selectable: selectable, selectAll: selectAll, selectedAll: selectedAll, sorterState: sorterState, sortingIcon: sortingIcon, sortingIconAscending: sortingIconAscending, sortingIconDescending: sortingIconDescending, handleFilterOnChange: function (key, event) {
                        return handleColumnFilterChange(key, event, 'change');
                    }, handleFilterOnInput: function (key, event) { return handleColumnFilterChange(key, event, 'input'); }, handleOnCustomFilterChange: function (key, event) { return handleColumnFilterChange(key, event); }, handleSelectAllChecked: function () { return handleSelectAllChecked(); }, handleSort: function (key, index) { return handleSorterChange(key, index); } }))),
                React$1.createElement(CSmartTableBody, __assign$1({ clickableRows: clickableRows, currentItems: currentItems, firstItemOnActivePageIndex: firstItemOnActivePageIndex, noItemsLabel: noItemsLabel, onRowClick: function (item, index, columnName, event) {
                        return clickableRows && onRowClick && onRowClick(item, index, columnName, event);
                    }, onRowChecked: function (item, value) { return handleRowChecked(item, value); }, columnNames: columnNames, scopedColumns: scopedColumns, selectable: selectable, selected: _selected }, tableBodyProps)),
                typeof footer === 'boolean' && footer && (React$1.createElement(CSmartTableHead, __assign$1({ component: CTableFoot }, tableFootProps, { columnFilter: false, columnSorter: false, columns: columns !== null && columns !== void 0 ? columns : columnNames, items: _items, handleSelectAllChecked: function () { return handleSelectAllChecked(); }, selectable: selectable, selectAll: selectAll, selectedAll: selectedAll, showGroups: false }))),
                Array.isArray(footer) && (React$1.createElement(CTableFoot, __assign$1({}, tableFootProps),
                    React$1.createElement(CTableRow, null, footer.map(function (item, index) { return (React$1.createElement(CTableDataCell, __assign$1({}, (typeof item === 'object' && item._props && __assign$1({}, item._props)), { key: index }), typeof item === 'object' ? item.label : item)); }))))),
            loading && (React$1.createElement(CElementCover, { boundaries: [
                    { sides: ['top'], query: 'tbody' },
                    { sides: ['bottom'], query: 'tbody' },
                ] }, elementCover))),
        (pagination || itemsPerPageSelect) && (React$1.createElement("div", { className: "row" },
            React$1.createElement("div", { className: "col" }, ((pagination && numberOfPages > 1) || (paginationProps && paginationProps.pages > 1)) && (React$1.createElement(CSmartPagination, __assign$1({ activePage: _activePage, onActivePageChange: function (page) {
                    pagination && typeof pagination === 'object' && pagination.external
                        ? onActivePageChange && onActivePageChange(page)
                        : setActivePage(page);
                }, pages: numberOfPages }, paginationProps)))),
            React$1.createElement("div", { className: "col-auto ms-auto" }, itemsPerPageSelect && (React$1.createElement("div", { className: "row" },
                React$1.createElement(CFormLabel, { className: "col-auto col-form-label" }, itemsPerPageLabel),
                React$1.createElement("div", { className: "col-auto" },
                    React$1.createElement(CFormSelect, { defaultValue: _itemsPerPage, onChange: function (event) {
                            return handleItemsPerPageChange(event);
                        } }, itemsPerPageOptions &&
                        itemsPerPageOptions.map(function (number, index) {
                            return (React$1.createElement("option", { value: number, key: index }, number));
                        }))))))))));
});
CSmartTable.propTypes = {
    activePage: PropTypes$1.number,
    cleaner: PropTypes$1.bool,
    clickableRows: PropTypes$1.bool,
    columnFilter: PropTypes$1.oneOfType([PropTypes$1.bool, PropTypes$1.object]),
    columnFilterValue: PropTypes$1.object,
    columns: PropTypes$1.array,
    columnSorter: PropTypes$1.oneOfType([PropTypes$1.bool, PropTypes$1.object]),
    elementCover: PropTypes$1.node,
    footer: PropTypes$1.oneOfType([PropTypes$1.bool, PropTypes$1.array]),
    header: PropTypes$1.bool,
    items: PropTypes$1.array,
    itemsNumber: PropTypes$1.number,
    itemsPerPage: PropTypes$1.number,
    itemsPerPageLabel: PropTypes$1.string,
    itemsPerPageOptions: PropTypes$1.array,
    itemsPerPageSelect: PropTypes$1.oneOfType([PropTypes$1.bool, PropTypes$1.object]),
    loading: PropTypes$1.bool,
    noItemsLabel: PropTypes$1.oneOfType([PropTypes$1.string, PropTypes$1.node]),
    onActivePageChange: PropTypes$1.func,
    onColumnFilterChange: PropTypes$1.func,
    onFilteredItemsChange: PropTypes$1.func,
    onItemsPerPageChange: PropTypes$1.func,
    onRowClick: PropTypes$1.func,
    onSelectAll: PropTypes$1.func,
    onSelectedItemsChange: PropTypes$1.func,
    onSorterChange: PropTypes$1.func,
    onTableFilterChange: PropTypes$1.func,
    pagination: PropTypes$1.oneOfType([PropTypes$1.bool, PropTypes$1.object]),
    paginationProps: PropTypes$1.any,
    scopedColumns: PropTypes$1.object,
    selectable: PropTypes$1.bool,
    selectAll: PropTypes$1.oneOfType([PropTypes$1.bool, PropTypes$1.object]),
    selected: PropTypes$1.array,
    sorterValue: PropTypes$1.object,
    sortingIcon: PropTypes$1.node,
    sortingIconAscending: PropTypes$1.node,
    sortingIconDescending: PropTypes$1.node,
    tableBodyProps: PropTypes$1.object,
    tableFootProps: PropTypes$1.object,
    tableFilter: PropTypes$1.oneOfType([PropTypes$1.bool, PropTypes$1.object]),
    tableFilterLabel: PropTypes$1.string,
    tableFilterPlaceholder: PropTypes$1.string,
    tableFilterValue: PropTypes$1.string,
    tableHeadProps: PropTypes$1.object,
    tableProps: PropTypes$1.object,
};
CSmartTable.displayName = 'CSmartTable';

var isOnMobile = function (element) {
    return Boolean(getComputedStyle(element).getPropertyValue('--cui-is-mobile'));
};
var CSidebar = React$1.forwardRef(function (_a, ref) {
    var _b;
    var children = _a.children, className = _a.className, colorScheme = _a.colorScheme, narrow = _a.narrow, onHide = _a.onHide, onShow = _a.onShow, onVisibleChange = _a.onVisibleChange, overlaid = _a.overlaid, placement = _a.placement, position = _a.position, size = _a.size, unfoldable = _a.unfoldable, visible = _a.visible, rest = __rest$1(_a, ["children", "className", "colorScheme", "narrow", "onHide", "onShow", "onVisibleChange", "overlaid", "placement", "position", "size", "unfoldable", "visible"]);
    var sidebarRef = React$1.useRef(null);
    var forkedRef = useForkedRef(ref, sidebarRef);
    var _c = React$1.useState(false), mobile = _c[0], setMobile = _c[1];
    var _d = React$1.useState(visible), _visible = _d[0], setVisible = _d[1];
    var _e = React$1.useState(), inViewport = _e[0], setInViewport = _e[1];
    React$1.useEffect(function () {
        sidebarRef.current && setMobile(isOnMobile(sidebarRef.current));
        setVisible(visible);
    }, [visible]);
    React$1.useEffect(function () {
        inViewport !== undefined && onVisibleChange && onVisibleChange(inViewport);
        !inViewport && onHide && onHide();
        inViewport && onShow && onShow();
    }, [inViewport]);
    React$1.useEffect(function () {
        mobile && visible && setVisible(false);
    }, [mobile]);
    React$1.useEffect(function () {
        var _a, _b;
        sidebarRef.current && setMobile(isOnMobile(sidebarRef.current));
        sidebarRef.current && setInViewport(isInViewport(sidebarRef.current));
        window.addEventListener('resize', handleResize);
        window.addEventListener('mouseup', handleClickOutside);
        window.addEventListener('keyup', handleKeyup);
        (_a = sidebarRef.current) === null || _a === void 0 ? void 0 : _a.addEventListener('mouseup', handleOnClick);
        (_b = sidebarRef.current) === null || _b === void 0 ? void 0 : _b.addEventListener('transitionend', function () {
            sidebarRef.current && setInViewport(isInViewport(sidebarRef.current));
        });
        return function () {
            var _a, _b;
            window.removeEventListener('resize', handleResize);
            window.removeEventListener('mouseup', handleClickOutside);
            window.removeEventListener('keyup', handleKeyup);
            (_a = sidebarRef.current) === null || _a === void 0 ? void 0 : _a.removeEventListener('mouseup', handleOnClick);
            (_b = sidebarRef.current) === null || _b === void 0 ? void 0 : _b.removeEventListener('transitionend', function () {
                sidebarRef.current && setInViewport(isInViewport(sidebarRef.current));
            });
        };
    });
    var handleHide = function () {
        setVisible(false);
    };
    var handleResize = function () {
        sidebarRef.current && setMobile(isOnMobile(sidebarRef.current));
        sidebarRef.current && setInViewport(isInViewport(sidebarRef.current));
    };
    var handleKeyup = function (event) {
        if (mobile &&
            sidebarRef.current &&
            !sidebarRef.current.contains(event.target)) {
            handleHide();
        }
    };
    var handleClickOutside = function (event) {
        if (mobile &&
            sidebarRef.current &&
            !sidebarRef.current.contains(event.target)) {
            handleHide();
        }
    };
    var handleOnClick = function (event) {
        var target = event.target;
        target &&
            target.classList.contains('nav-link') &&
            !target.classList.contains('nav-group-toggle') &&
            mobile &&
            handleHide();
    };
    return (React$1.createElement(React$1.Fragment, null,
        React$1.createElement("div", __assign$1({ className: classNames$1('sidebar', (_b = {},
                _b["sidebar-".concat(colorScheme)] = colorScheme,
                _b['sidebar-narrow'] = narrow,
                _b['sidebar-overlaid'] = overlaid,
                _b["sidebar-".concat(placement)] = placement,
                _b["sidebar-".concat(position)] = position,
                _b["sidebar-".concat(size)] = size,
                _b['sidebar-narrow-unfoldable'] = unfoldable,
                _b.show = _visible === true && mobile,
                _b.hide = _visible === false && !mobile,
                _b), className) }, rest, { ref: forkedRef }), children),
        typeof window !== 'undefined' &&
            mobile &&
            ReactDOM.createPortal(React$1.createElement(CBackdrop, { className: "sidebar-backdrop", visible: _visible }), document.body)));
});
CSidebar.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    colorScheme: PropTypes$1.oneOf(['dark', 'light']),
    narrow: PropTypes$1.bool,
    onHide: PropTypes$1.func,
    onShow: PropTypes$1.func,
    onVisibleChange: PropTypes$1.func,
    overlaid: PropTypes$1.bool,
    placement: PropTypes$1.oneOf(['start', 'end']),
    position: PropTypes$1.oneOf(['fixed', 'sticky']),
    size: PropTypes$1.oneOf(['sm', 'lg', 'xl']),
    unfoldable: PropTypes$1.bool,
    visible: PropTypes$1.bool,
};
CSidebar.displayName = 'CSidebar';

var CSidebarBrand = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, rest = __rest$1(_a, ["children", "className"]);
    return (React$1.createElement("div", __assign$1({ className: classNames$1('sidebar-brand', className), ref: ref }, rest), children));
});
CSidebarBrand.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
};
CSidebarBrand.displayName = 'CSidebarBrand';

var CSidebarFooter = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, rest = __rest$1(_a, ["children", "className"]);
    return (React$1.createElement("div", __assign$1({ className: classNames$1('sidebar-footer', className), ref: ref }, rest), children));
});
CSidebarFooter.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
};
CSidebarFooter.displayName = 'CSidebarFooter';

var CSidebarToggler = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, rest = __rest$1(_a, ["children", "className"]);
    return (React$1.createElement("button", __assign$1({ className: classNames$1('sidebar-toggler', className), ref: ref }, rest), children));
});
CSidebarToggler.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
};
CSidebarToggler.displayName = 'CSidebarToggler';

var CSidebarHeader = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, rest = __rest$1(_a, ["children", "className"]);
    return (React$1.createElement("div", __assign$1({ className: classNames$1('sidebar-header', className), ref: ref }, rest), children));
});
CSidebarHeader.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
};
CSidebarHeader.displayName = 'CSidebarHeader';

var CTabContent = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, rest = __rest$1(_a, ["children", "className"]);
    return (React$1.createElement("div", __assign$1({ className: classNames$1('tab-content', className) }, rest, { ref: ref }), children));
});
CTabContent.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
};
CTabContent.displayName = 'CTabContent';

var CTabPane = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, onHide = _a.onHide, onShow = _a.onShow, visible = _a.visible, rest = __rest$1(_a, ["children", "className", "onHide", "onShow", "visible"]);
    var tabPaneRef = React$1.useRef();
    var forkedRef = useForkedRef(ref, tabPaneRef);
    return (React$1.createElement(Transition$1, { in: visible, nodeRef: tabPaneRef, onEnter: onShow, onExit: onHide, timeout: 150 }, function (state) { return (React$1.createElement("div", __assign$1({ className: classNames$1('tab-pane', 'fade', {
            active: visible,
            show: state === 'entered',
        }, className) }, rest, { ref: forkedRef }), children)); }));
});
CTabPane.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    onHide: PropTypes$1.func,
    onShow: PropTypes$1.func,
    visible: PropTypes$1.bool,
};
CTabPane.displayName = 'CTabPane';

var CToastContext = React$1.createContext({});
var CToast = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, _b = _a.animation, animation = _b === void 0 ? true : _b, _c = _a.autohide, autohide = _c === void 0 ? true : _c, className = _a.className, color = _a.color, _d = _a.delay, delay = _d === void 0 ? 5000 : _d, index = _a.index, key = _a.key, _e = _a.visible, visible = _e === void 0 ? false : _e, onClose = _a.onClose, onShow = _a.onShow, rest = __rest$1(_a, ["children", "animation", "autohide", "className", "color", "delay", "index", "key", "visible", "onClose", "onShow"]);
    var toastRef = React$1.useRef();
    var forkedRef = useForkedRef(ref, toastRef);
    var _f = React$1.useState(false), _visible = _f[0], setVisible = _f[1];
    var timeout = React$1.useRef();
    React$1.useEffect(function () {
        setVisible(visible);
    }, [visible]);
    var contextValues = {
        visible: _visible,
        setVisible: setVisible,
    };
    // triggered on mount and destroy
    React$1.useEffect(function () { return function () { return clearTimeout(timeout.current); }; }, []);
    React$1.useEffect(function () {
        _autohide();
    }, [_visible]);
    var _autohide = function () {
        if (autohide) {
            clearTimeout(timeout.current);
            timeout.current = window.setTimeout(function () {
                setVisible(false);
            }, delay);
        }
    };
    return (React$1.createElement(Transition$1, { in: _visible, nodeRef: toastRef, onEnter: function () { return onShow && onShow(index !== null && index !== void 0 ? index : null); }, onExited: function () { return onClose && onClose(index !== null && index !== void 0 ? index : null); }, timeout: 250, unmountOnExit: true }, function (state) {
        var _a;
        return (React$1.createElement(CToastContext.Provider, { value: contextValues },
            React$1.createElement("div", __assign$1({ className: classNames$1('toast', (_a = {
                        fade: animation
                    },
                    _a["bg-".concat(color)] = color,
                    _a['border-0'] = color,
                    _a['show showing'] = state === 'entering' || state === 'exiting',
                    _a.show = state === 'entered',
                    _a), className), "aria-live": "assertive", "aria-atomic": "true", role: "alert", onMouseEnter: function () { return clearTimeout(timeout.current); }, onMouseLeave: function () { return _autohide(); } }, rest, { key: key, ref: forkedRef }), children)));
    }));
});
CToast.propTypes = {
    animation: PropTypes$1.bool,
    autohide: PropTypes$1.bool,
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    color: colorPropType,
    delay: PropTypes$1.number,
    index: PropTypes$1.number,
    key: PropTypes$1.number,
    onClose: PropTypes$1.func,
    onShow: PropTypes$1.func,
    visible: PropTypes$1.bool,
};
CToast.displayName = 'CToast';

var CToastBody = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, rest = __rest$1(_a, ["children", "className"]);
    return (React$1.createElement("div", __assign$1({ className: classNames$1('toast-body', className) }, rest, { ref: ref }), children));
});
CToastBody.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
};
CToastBody.displayName = 'CToastBody';

var CToastClose = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, Component = _a.component, rest = __rest$1(_a, ["children", "component"]);
    var setVisible = React$1.useContext(CToastContext).setVisible;
    return Component ? (React$1.createElement(Component, __assign$1({ onClick: function () { return setVisible(false); } }, rest, { ref: ref }), children)) : (React$1.createElement(CCloseButton, __assign$1({ onClick: function () { return setVisible(false); } }, rest, { ref: ref })));
});
CToastClose.propTypes = __assign$1(__assign$1({}, CCloseButton.propTypes), { component: PropTypes$1.elementType });
CToastClose.displayName = 'CToastClose';

var CToastHeader = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, closeButton = _a.closeButton, rest = __rest$1(_a, ["children", "className", "closeButton"]);
    return (React$1.createElement("div", __assign$1({ className: classNames$1('toast-header', className) }, rest, { ref: ref }),
        children,
        closeButton && React$1.createElement(CToastClose, null)));
});
CToastHeader.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    closeButton: PropTypes$1.bool,
};
CToastHeader.displayName = 'CToastHeader';

var CToaster = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, className = _a.className, placement = _a.placement, push = _a.push, rest = __rest$1(_a, ["children", "className", "placement", "push"]);
    var _b = React$1.useState([]), toasts = _b[0], setToasts = _b[1];
    var index = React$1.useRef(0);
    React$1.useEffect(function () {
        index.current++;
        push && addToast(push);
    }, [push]);
    var addToast = function (push) {
        setToasts(function (state) { return __spreadArray(__spreadArray([], state, true), [
            React$1.cloneElement(push, {
                index: index.current,
                key: index.current,
                onClose: function (index) {
                    return setToasts(function (state) { return state.filter(function (i) { return i.props.index !== index; }); });
                },
            }),
        ], false); });
    };
    return (React$1.createElement(CConditionalPortal, { portal: typeof placement === 'string' }, toasts.length > 0 || children ? (React$1.createElement("div", __assign$1({ className: classNames$1('toaster toast-container p-3', {
            'position-fixed': placement,
            'top-0': placement && placement.includes('top'),
            'top-50 translate-middle-y': placement && placement.includes('middle'),
            'bottom-0': placement && placement.includes('bottom'),
            'start-0': placement && placement.includes('start'),
            'start-50 translate-middle-x': placement && placement.includes('center'),
            'end-0': placement && placement.includes('end'),
        }, className) }, rest, { ref: ref }),
        children,
        toasts.map(function (toast) { return React$1.cloneElement(toast, { visible: true }); }))) : null));
});
CToaster.propTypes = {
    children: PropTypes$1.node,
    className: PropTypes$1.string,
    placement: PropTypes$1.oneOfType([
        PropTypes$1.string,
        PropTypes$1.oneOf([
            'top-start',
            'top-center',
            'top-end',
            'middle-start',
            'middle-center',
            'middle-end',
            'bottom-start',
            'bottom-center',
            'bottom-end',
        ]),
    ]),
    push: PropTypes$1.any,
};
CToaster.displayName = 'CToaster';

var CTooltip = React$1.forwardRef(function (_a, ref) {
    var children = _a.children, _b = _a.animation, animation = _b === void 0 ? true : _b, className = _a.className, container = _a.container, content = _a.content, _c = _a.delay, delay = _c === void 0 ? 0 : _c, _d = _a.fallbackPlacements, fallbackPlacements = _d === void 0 ? ['top', 'right', 'bottom', 'left'] : _d, _e = _a.offset, offset = _e === void 0 ? [0, 6] : _e, onHide = _a.onHide; _a.onShow; var _f = _a.placement, placement = _f === void 0 ? 'top' : _f, _g = _a.trigger, trigger = _g === void 0 ? ['hover', 'focus'] : _g, visible = _a.visible, rest = __rest$1(_a, ["children", "animation", "className", "container", "content", "delay", "fallbackPlacements", "offset", "onHide", "onShow", "placement", "trigger", "visible"]);
    var tooltipRef = React$1.useRef(null);
    var togglerRef = React$1.useRef(null);
    var forkedRef = useForkedRef(ref, tooltipRef);
    var uID = React$1.useRef("tooltip".concat(Math.floor(Math.random() * 1000000)));
    var _h = usePopper(), initPopper = _h.initPopper, destroyPopper = _h.destroyPopper;
    var _j = React$1.useState(visible), _visible = _j[0], setVisible = _j[1];
    var _delay = typeof delay === 'number' ? { show: delay, hide: delay } : delay;
    var popperConfig = {
        modifiers: [
            {
                name: 'arrow',
                options: {
                    element: '.tooltip-arrow',
                },
            },
            {
                name: 'flip',
                options: {
                    fallbackPlacements: fallbackPlacements,
                },
            },
            {
                name: 'offset',
                options: {
                    offset: offset,
                },
            },
        ],
        placement: getRTLPlacement(placement, togglerRef.current),
    };
    React$1.useEffect(function () {
        setVisible(visible);
    }, [visible]);
    var toggleVisible = function (visible) {
        if (visible) {
            setTimeout(function () { return setVisible(true); }, _delay.show);
            return;
        }
        setTimeout(function () { return setVisible(false); }, _delay.hide);
    };
    return (React$1.createElement(React$1.Fragment, null,
        React$1.cloneElement(children, __assign$1(__assign$1(__assign$1(__assign$1(__assign$1({}, (_visible && {
            'aria-describedby': uID.current,
        })), { ref: togglerRef }), ((trigger === 'click' || trigger.includes('click')) && {
            onClick: function () { return toggleVisible(!_visible); },
        })), ((trigger === 'focus' || trigger.includes('focus')) && {
            onFocus: function () { return toggleVisible(true); },
            onBlur: function () { return toggleVisible(false); },
        })), ((trigger === 'hover' || trigger.includes('hover')) && {
            onMouseEnter: function () { return toggleVisible(true); },
            onMouseLeave: function () { return toggleVisible(false); },
        }))),
        React$1.createElement(CConditionalPortal, { container: container, portal: true },
            React$1.createElement(Transition$1, { in: _visible, mountOnEnter: true, nodeRef: tooltipRef, onEnter: function () {
                    if (togglerRef.current && tooltipRef.current) {
                        initPopper(togglerRef.current, tooltipRef.current, popperConfig);
                    }
                }, onEntering: function () {
                    if (togglerRef.current && tooltipRef.current) {
                        tooltipRef.current.style.display = 'initial';
                    }
                }, onExit: onHide, onExited: function () {
                    destroyPopper();
                }, timeout: {
                    enter: 0,
                    exit: tooltipRef.current
                        ? getTransitionDurationFromElement(tooltipRef.current) + 50
                        : 200,
                }, unmountOnExit: true }, function (state) { return (React$1.createElement("div", __assign$1({ className: classNames$1('tooltip', 'bs-tooltip-auto', {
                    fade: animation,
                    show: state === 'entered',
                }, className), id: uID.current, ref: forkedRef, role: "tooltip", style: {
                    display: 'none',
                } }, rest),
                React$1.createElement("div", { className: "tooltip-arrow" }),
                React$1.createElement("div", { className: "tooltip-inner" }, content))); }))));
});
CTooltip.propTypes = {
    animation: PropTypes$1.bool,
    children: PropTypes$1.node,
    container: PropTypes$1.any,
    content: PropTypes$1.oneOfType([PropTypes$1.string, PropTypes$1.node]),
    delay: PropTypes$1.oneOfType([
        PropTypes$1.number,
        PropTypes$1.shape({
            show: PropTypes$1.number.isRequired,
            hide: PropTypes$1.number.isRequired,
        }),
    ]),
    fallbackPlacements: fallbackPlacementsPropType,
    offset: PropTypes$1.any,
    onHide: PropTypes$1.func,
    onShow: PropTypes$1.func,
    placement: PropTypes$1.oneOf(['auto', 'top', 'right', 'bottom', 'left']),
    trigger: triggerPropType,
    visible: PropTypes$1.bool,
};
CTooltip.displayName = 'CTooltip';

var CWidgetStatsA = React$1.forwardRef(function (_a, ref) {
    var _b;
    var action = _a.action, chart = _a.chart, className = _a.className, color = _a.color, title = _a.title, value = _a.value, rest = __rest$1(_a, ["action", "chart", "className", "color", "title", "value"]);
    return (React$1.createElement(CCard, __assign$1({ className: classNames$1((_b = {}, _b["bg-".concat(color)] = color, _b['text-high-emphasis-inverse'] = color, _b), className) }, rest, { ref: ref }),
        React$1.createElement(CCardBody, { className: "pb-0 d-flex justify-content-between align-items-start" },
            React$1.createElement("div", null,
                value && React$1.createElement("div", { className: "fs-4 fw-semibold" }, value),
                title && React$1.createElement("div", null, title)),
            action),
        chart));
});
CWidgetStatsA.propTypes = {
    action: PropTypes$1.node,
    chart: PropTypes$1.oneOfType([PropTypes$1.string, PropTypes$1.node]),
    className: PropTypes$1.string,
    color: colorPropType,
    title: PropTypes$1.oneOfType([PropTypes$1.string, PropTypes$1.node]),
    value: PropTypes$1.oneOfType([PropTypes$1.string, PropTypes$1.node, PropTypes$1.number]),
};
CWidgetStatsA.displayName = 'CWidgetStatsA';

var CWidgetStatsB = React$1.forwardRef(function (_a, ref) {
    var className = _a.className, color = _a.color, inverse = _a.inverse, progress = _a.progress, text = _a.text, title = _a.title, value = _a.value, rest = __rest$1(_a, ["className", "color", "inverse", "progress", "text", "title", "value"]);
    return (React$1.createElement(CCard, __assign$1({ className: className, color: color }, (inverse && { textColor: 'high-emphasis-inverse' }), rest, { ref: ref }),
        React$1.createElement(CCardBody, null,
            value && React$1.createElement("div", { className: "fs-4 fw-semibold" }, value),
            title && React$1.createElement("div", null, title),
            React$1.createElement(CProgress, __assign$1({ className: "my-2", height: 4 }, (inverse && { white: true }), progress)),
            text && (React$1.createElement("small", { className: inverse ? 'text-medium-emphasis-inverse' : 'text-medium-emphasis' }, text)))));
});
CWidgetStatsB.propTypes = {
    className: PropTypes$1.string,
    color: colorPropType,
    inverse: PropTypes$1.bool,
    progress: PropTypes$1.object,
    text: PropTypes$1.string,
    title: PropTypes$1.oneOfType([PropTypes$1.string, PropTypes$1.node]),
    value: PropTypes$1.oneOfType([PropTypes$1.string, PropTypes$1.node, PropTypes$1.number]),
};
CWidgetStatsB.displayName = 'CWidgetCWidgetStatsB';

var CWidgetStatsC = React$1.forwardRef(function (_a, ref) {
    var className = _a.className, color = _a.color, icon = _a.icon, inverse = _a.inverse, progress = _a.progress, title = _a.title, value = _a.value, rest = __rest$1(_a, ["className", "color", "icon", "inverse", "progress", "title", "value"]);
    return (React$1.createElement(CCard, __assign$1({ className: className, color: color }, (inverse && { textColor: 'high-emphasis-inverse' }), rest, { ref: ref }),
        React$1.createElement(CCardBody, null,
            icon && (React$1.createElement("div", { className: "text-medium-emphasis".concat(inverse ? '-inverse' : '', " text-end mb-4") }, icon)),
            value && (React$1.createElement("div", { className: "text-high-emphasis".concat(inverse ? '-inverse' : '', " fs-4 fw-semibold") }, value)),
            title && (React$1.createElement("div", { className: inverse ? 'text-medium-emphasis-inverse' : 'text-medium-emphasis' }, title)),
            React$1.createElement(CProgress, __assign$1({ className: "mt-3 mb-0", height: 4 }, (inverse && { white: true }), progress)))));
});
CWidgetStatsC.propTypes = {
    className: PropTypes$1.string,
    color: colorPropType,
    icon: PropTypes$1.oneOfType([PropTypes$1.string, PropTypes$1.node]),
    inverse: PropTypes$1.bool,
    progress: PropTypes$1.object,
    title: PropTypes$1.oneOfType([PropTypes$1.string, PropTypes$1.node]),
    value: PropTypes$1.oneOfType([PropTypes$1.string, PropTypes$1.node, PropTypes$1.number]),
};
CWidgetStatsC.displayName = 'CWidgetStatsCWidgetStatsC';

var CWidgetStatsD = React$1.forwardRef(function (_a, ref) {
    var _b;
    var className = _a.className, chart = _a.chart, color = _a.color, icon = _a.icon, values = _a.values, rest = __rest$1(_a, ["className", "chart", "color", "icon", "values"]);
    return (React$1.createElement(CCard, __assign$1({ className: className }, rest, { ref: ref }),
        React$1.createElement(CCardHeader, { className: classNames$1('position-relative d-flex justify-content-center align-items-center', (_b = {},
                _b["bg-".concat(color)] = color,
                _b)) },
            icon,
            chart),
        React$1.createElement(CCardBody, { className: "row text-center" }, values &&
            values.map(function (value, index) {
                return (React$1.createElement(React$1.Fragment, { key: index },
                    index % 2 !== 0 && React$1.createElement("div", { className: "vr" }),
                    React$1.createElement(CCol, null,
                        React$1.createElement("div", { className: "fs-5 fw-semibold" }, value.value),
                        React$1.createElement("div", { className: "text-uppercase text-medium-emphasis small" }, value.title))));
            }))));
});
CWidgetStatsD.propTypes = {
    chart: PropTypes$1.oneOfType([PropTypes$1.string, PropTypes$1.node]),
    className: PropTypes$1.string,
    color: colorPropType,
    icon: PropTypes$1.oneOfType([PropTypes$1.string, PropTypes$1.node]),
    values: PropTypes$1.arrayOf(PropTypes$1.any),
};
CWidgetStatsD.displayName = 'CWidgetStatsD';

var CWidgetStatsE = React$1.forwardRef(function (_a, ref) {
    var chart = _a.chart, className = _a.className, title = _a.title, value = _a.value, rest = __rest$1(_a, ["chart", "className", "title", "value"]);
    return (React$1.createElement(CCard, __assign$1({ className: classNames$1(className) }, rest, { ref: ref }),
        React$1.createElement(CCardBody, { className: "text-center" },
            title && (React$1.createElement("div", { className: "text-medium-emphasis small text-uppercase fw-semibold" }, title)),
            value && React$1.createElement("div", { className: "fs-6 fw-semibold py-3" }, value),
            chart)));
});
CWidgetStatsE.propTypes = {
    children: PropTypes$1.node,
    chart: PropTypes$1.oneOfType([PropTypes$1.string, PropTypes$1.node]),
    className: PropTypes$1.string,
    title: PropTypes$1.oneOfType([PropTypes$1.string, PropTypes$1.node]),
    value: PropTypes$1.oneOfType([PropTypes$1.string, PropTypes$1.node, PropTypes$1.number]),
};
CWidgetStatsE.displayName = 'CWidgetStatsE';

var CWidgetStatsF = React$1.forwardRef(function (_a, ref) {
    var className = _a.className, color = _a.color, footer = _a.footer, icon = _a.icon, _b = _a.padding, padding = _b === void 0 ? true : _b, title = _a.title, value = _a.value, rest = __rest$1(_a, ["className", "color", "footer", "icon", "padding", "title", "value"]);
    return (React$1.createElement(CCard, __assign$1({ className: className }, rest, { ref: ref }),
        React$1.createElement(CCardBody, { className: "d-flex align-items-center ".concat(padding === false && 'p-0') },
            React$1.createElement("div", { className: "me-3 text-white bg-".concat(color, " ").concat(padding ? 'p-3' : 'p-4') }, icon),
            React$1.createElement("div", null,
                React$1.createElement("div", { className: "fs-6 fw-semibold text-".concat(color) }, value),
                React$1.createElement("div", { className: "text-medium-emphasis text-uppercase fw-semibold small" }, title))),
        footer && React$1.createElement(CCardFooter, null, footer)));
});
CWidgetStatsF.propTypes = {
    className: PropTypes$1.string,
    color: colorPropType,
    footer: PropTypes$1.oneOfType([PropTypes$1.string, PropTypes$1.node]),
    icon: PropTypes$1.oneOfType([PropTypes$1.string, PropTypes$1.node]),
    padding: PropTypes$1.bool,
    title: PropTypes$1.oneOfType([PropTypes$1.string, PropTypes$1.node]),
    value: PropTypes$1.oneOfType([PropTypes$1.string, PropTypes$1.node, PropTypes$1.number]),
};
CWidgetStatsF.displayName = 'CWidgetStatsF';

exports.CAccordion = CAccordion;
exports.CAccordionBody = CAccordionBody;
exports.CAccordionButton = CAccordionButton;
exports.CAccordionHeader = CAccordionHeader;
exports.CAccordionItem = CAccordionItem;
exports.CAlert = CAlert;
exports.CAlertHeading = CAlertHeading;
exports.CAlertLink = CAlertLink;
exports.CAvatar = CAvatar;
exports.CBackdrop = CBackdrop;
exports.CBadge = CBadge;
exports.CBreadcrumb = CBreadcrumb;
exports.CBreadcrumbItem = CBreadcrumbItem;
exports.CButton = CButton;
exports.CButtonGroup = CButtonGroup;
exports.CButtonToolbar = CButtonToolbar;
exports.CCallout = CCallout;
exports.CCard = CCard;
exports.CCardBody = CCardBody;
exports.CCardFooter = CCardFooter;
exports.CCardGroup = CCardGroup;
exports.CCardHeader = CCardHeader;
exports.CCardImage = CCardImage;
exports.CCardImageOverlay = CCardImageOverlay;
exports.CCardLink = CCardLink;
exports.CCardSubtitle = CCardSubtitle;
exports.CCardText = CCardText;
exports.CCardTitle = CCardTitle;
exports.CCarousel = CCarousel;
exports.CCarouselCaption = CCarouselCaption;
exports.CCarouselItem = CCarouselItem;
exports.CCloseButton = CCloseButton;
exports.CCol = CCol;
exports.CCollapse = CCollapse;
exports.CConditionalPortal = CConditionalPortal;
exports.CContainer = CContainer;
exports.CDatePicker = CDatePicker;
exports.CDateRangePicker = CDateRangePicker;
exports.CDropdown = CDropdown;
exports.CDropdownDivider = CDropdownDivider;
exports.CDropdownHeader = CDropdownHeader;
exports.CDropdownItem = CDropdownItem;
exports.CDropdownItemPlain = CDropdownItemPlain;
exports.CDropdownMenu = CDropdownMenu;
exports.CDropdownToggle = CDropdownToggle;
exports.CElementCover = CElementCover;
exports.CFooter = CFooter;
exports.CForm = CForm;
exports.CFormCheck = CFormCheck;
exports.CFormControlValidation = CFormControlValidation;
exports.CFormControlWrapper = CFormControlWrapper;
exports.CFormFeedback = CFormFeedback;
exports.CFormFloating = CFormFloating;
exports.CFormInput = CFormInput;
exports.CFormLabel = CFormLabel;
exports.CFormRange = CFormRange;
exports.CFormSelect = CFormSelect;
exports.CFormSwitch = CFormSwitch;
exports.CFormText = CFormText;
exports.CFormTextarea = CFormTextarea;
exports.CHeader = CHeader;
exports.CHeaderBrand = CHeaderBrand;
exports.CHeaderDivider = CHeaderDivider;
exports.CHeaderNav = CHeaderNav;
exports.CHeaderText = CHeaderText;
exports.CHeaderToggler = CHeaderToggler;
exports.CImage = CImage;
exports.CInputGroup = CInputGroup;
exports.CInputGroupText = CInputGroupText;
exports.CLink = CLink;
exports.CListGroup = CListGroup;
exports.CListGroupItem = CListGroupItem;
exports.CLoadingButton = CLoadingButton;
exports.CModal = CModal;
exports.CModalBody = CModalBody;
exports.CModalContent = CModalContent;
exports.CModalDialog = CModalDialog;
exports.CModalFooter = CModalFooter;
exports.CModalHeader = CModalHeader;
exports.CModalTitle = CModalTitle;
exports.CMultiSelect = CMultiSelect;
exports.CNav = CNav;
exports.CNavGroup = CNavGroup;
exports.CNavGroupItems = CNavGroupItems;
exports.CNavItem = CNavItem;
exports.CNavLink = CNavLink;
exports.CNavTitle = CNavTitle;
exports.CNavbar = CNavbar;
exports.CNavbarBrand = CNavbarBrand;
exports.CNavbarNav = CNavbarNav;
exports.CNavbarText = CNavbarText;
exports.CNavbarToggler = CNavbarToggler;
exports.COffcanvas = COffcanvas;
exports.COffcanvasBody = COffcanvasBody;
exports.COffcanvasHeader = COffcanvasHeader;
exports.COffcanvasTitle = COffcanvasTitle;
exports.CPagination = CPagination;
exports.CPaginationItem = CPaginationItem;
exports.CPlaceholder = CPlaceholder;
exports.CPopover = CPopover;
exports.CProgress = CProgress;
exports.CProgressBar = CProgressBar;
exports.CProgressStacked = CProgressStacked;
exports.CRow = CRow;
exports.CSidebar = CSidebar;
exports.CSidebarBrand = CSidebarBrand;
exports.CSidebarFooter = CSidebarFooter;
exports.CSidebarHeader = CSidebarHeader;
exports.CSidebarNav = CSidebarNav;
exports.CSidebarToggler = CSidebarToggler;
exports.CSmartPagination = CSmartPagination;
exports.CSmartTable = CSmartTable;
exports.CSpinner = CSpinner;
exports.CTabContent = CTabContent;
exports.CTabPane = CTabPane;
exports.CTable = CTable;
exports.CTableBody = CTableBody;
exports.CTableCaption = CTableCaption;
exports.CTableDataCell = CTableDataCell;
exports.CTableFoot = CTableFoot;
exports.CTableHead = CTableHead;
exports.CTableHeaderCell = CTableHeaderCell;
exports.CTableRow = CTableRow;
exports.CTimePicker = CTimePicker;
exports.CToast = CToast;
exports.CToastBody = CToastBody;
exports.CToastClose = CToastClose;
exports.CToastHeader = CToastHeader;
exports.CToaster = CToaster;
exports.CTooltip = CTooltip;
exports.CVirtualScroller = CVirtualScroller;
exports.CWidgetStatsA = CWidgetStatsA;
exports.CWidgetStatsB = CWidgetStatsB;
exports.CWidgetStatsC = CWidgetStatsC;
exports.CWidgetStatsD = CWidgetStatsD;
exports.CWidgetStatsE = CWidgetStatsE;
exports.CWidgetStatsF = CWidgetStatsF;
exports.useDebouncedCallback = useDebouncedCallback;
exports.useForkedRef = useForkedRef;
exports.useIsVisible = useIsVisible;
exports.usePopper = usePopper;
exports.useStateWithCallback = useStateWithCallback;
//# sourceMappingURL=index.js.map
