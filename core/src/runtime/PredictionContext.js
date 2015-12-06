var _ = require("lodash"),
    util = require('util'),
    Log4js = require('log4js');

function PredictionContext(cachedHashCode){
    this.cachedHashCode = cachedHashCode;
}

PredictionContext.fromRuleContext = function(atn, outerContext){
    if(outerContext == null)
        outerContext = 'EMPTY';
    if(outerContext.parent==null || outerContext == 'EMPTY')
        return 'EMPTY';
    var parent = PredictionContext.fromRuleContext(atn, outerContext.parent);
    var state = atn.states[outerContext.invokingState];
    var transition = state.transitions[0];
    return new SingletonPredictionContext(parent, transition.followState.stateNumber);
};

PredictionContext.merge = function(/*PredictionContext*/ a, /*PredictionContext*/ b,
                                   rootIsWildcard, mergeCache)
{
    if(!( a!=null && b!=null))
        throw new Error('assertion failure in PredictionContext.merge()'); // must be empty context, never null

    // share same graph if both same
    if ( a==b || a.equals(b) ) return a;

    if ( a instanceof SingletonPredictionContext && b instanceof SingletonPredictionContext) {
        return PredictionContext.mergeSingletons(a,b, rootIsWildcard, mergeCache);
    }

    // At least one of a or b is array
    // If one is $ and rootIsWildcard, return $ as * wildcard
    if ( rootIsWildcard ) {
        if ( a instanceof EmptyPredictionContext ) return a;
        if ( b instanceof EmptyPredictionContext ) return b;
    }

    // convert singleton so both are arrays to normalize
    if ( a instanceof SingletonPredictionContext ) {
        a = new ArrayPredictionContext(a);
    }
    if ( b instanceof SingletonPredictionContext) {
        b = new ArrayPredictionContext(b);
    }
    return mergeArrays(a, b, rootIsWildcard, mergeCache);
};

_.extend(PredictionContext, {
    mergeSingletons: function(a,b,rootIsWildcard, mergeCache){
        if ( mergeCache!=null ) {
            var previous = mergeCache.get(a,b);
            if ( previous!=null ) return previous;
            previous = mergeCache.get(b,a);
            if ( previous!=null ) return previous;
        }

        var rootMerge = PredictionContext.mergeRoot(a, b, rootIsWildcard);
        if ( rootMerge!=null ) {
            if ( mergeCache!=null ) mergeCache.put(a, b, rootMerge);
            return rootMerge;
        }

        if ( a.returnState==b.returnState ) { // a == b
            var parent = PredictionContext.merge(a.parent, b.parent, rootIsWildcard, mergeCache);
            // if parent is same as existing a or b parent or reduced to a parent, return it
            if ( parent == a.parent ) return a; // ax + bx = ax, if a=b
            if ( parent == b.parent ) return b; // ax + bx = bx, if a=b
            // else: ax + ay = a'[x,y]
            // merge parents x and y, giving array node with x,y then remainders
            // of those graphs.  dup a, a' points at merged array
            // new joined parent so create new singleton pointing to it, a'
            var a_ = SingletonPredictionContext.create(parent, a.returnState);
            if ( mergeCache!=null ) mergeCache.put(a, b, a_);
            return a_;
        }
        else { // a != b payloads differ
            // see if we can collapse parents due to $+x parents if local ctx
            var singleParent = null;
            if ( a==b || (a.parent!=null && a.parent.equals(b.parent)) ) { // ax + bx = [a,b]x
                singleParent = a.parent;
            }
            if ( singleParent!=null ) {	// parents are same
                // sort payloads and use same parent
                var payloads = [a.returnState, b.returnState];
                if ( a.returnState > b.returnState ) {
                    payloads[0] = b.returnState;
                    payloads[1] = a.returnState;
                }
                var parents = [singleParent, singleParent];
                var a_ = new ArrayPredictionContext(parents, payloads);
                if ( mergeCache!=null ) mergeCache.put(a, b, a_);
                return a_;
            }
            // parents differ and can't merge them. Just pack together
            // into array; can't merge.
            // ax + by = [ax,by]
            var payloads = [a.returnState, b.returnState];
            var parents = [a.parent, b.parent];
            if ( a.returnState > b.returnState ) { // sort by payload
                payloads[0] = b.returnState;
                payloads[1] = a.returnState;
                parents = [b.parent, a.parent];
            }
            var a_ = new ArrayPredictionContext(parents, payloads);
            if ( mergeCache!=null ) mergeCache.put(a, b, a_);
            return a_;
        }
    },

    mergeRoot:function( a, b, rootIsWildcard)
    {
        if ( rootIsWildcard ) {
            if ( a == PredictionContext.EMPTY ) return PredictionContext.EMPTY;  // * + b = *
            if ( b == PredictionContext.EMPTY ) return PredictionContext.EMPTY;  // a + * = *
        }
        else {
            if ( a == PredictionContext.EMPTY && b == PredictionContext.EMPTY ) return PredictionContext.EMPTY; // $ + $ = $
            if ( a == PredictionContext.EMPTY ) { // $ + x = [$,x]
                var payloads = [b.returnState, PredictionContext.EMPTY_RETURN_STATE];
                var parents = [b.parent, null];
                var joined =
                    new ArrayPredictionContext(parents, payloads);
                return joined;
            }
            if ( b == PredictionContext.EMPTY ) { // x + $ = [$,x] ($ is always first if present)
                var payloads = [a.returnState, EMPTY_RETURN_STATE];
                var parents = [a.parent, null];
                var joined =
                    new ArrayPredictionContext(parents, payloads);
                return joined;
            }
        }
        return null;
    },
    calculateHashCode:function(parent, returnState){
        if(Array.isArray(parent)){
            return PredictionContext._calculateHashCode(parent, returnState);
        }
        return JSON.stringify({
            p:parent.toString(),
            r:returnState
        });
    },

    _calculateHashCode:function( parents, returnStates) {
        var ps = [];
        parents.forEach(function(pa){
            ps.push(pa.hashCode());
        });

        return JSON.stringify({
            ps:ps,
            rs:returnStates
        });
    },
    calculateEmptyHashCode:function(){
        return '';
    }
});


PredictionContext.EMPTY_RETURN_STATE = 0xffffffff;
PredictionContext.prototype = {
    EMPTY_RETURN_STATE: PredictionContext.EMPTY_RETURN_STATE,

    isEmpty:function(){
        return this == PredictionContext.EMPTY;
    },
    toString:function(){
        return this.hashCode();
    },
    hasEmptyPath:function(){
        return this.getReturnState(this.size() - 1) == this.EMPTY_RETURN_STATE;
    },

    equals:function(o){
        return this === o;
    },

    hashCode: function() {
        return this.cachedHashCode;
    }
};

function SingletonPredictionContext(parent, returnState){
    PredictionContext.call(this,
        parent != null? PredictionContext.calculateHashCode(parent, returnState) : PredictionContext.calculateEmptyHashCode());
    if(returnState == -1) throw new Error('Invalid state number');
    this.parent = parent;
    this.returnState = returnState;
}

SingletonPredictionContext.create = function(parent, returnState){
    if ( returnState == this.EMPTY_RETURN_STATE && parent == null ) {
        // someone can pass in the bits of an array ctx that mean $
        return PredictionContext.EMPTY;
    }
    return new SingletonPredictionContext(parent, returnState);
};

SingletonPredictionContext.prototype = _.create(PredictionContext.prototype, {

    size:function(){
        return 1;
    },
    getReturnState:function(){
        return this.returnState;
    },
    getParent:function(index){
        return this.parent;
    },

    equals:function(o) {
        if (this == o) {
            return true;
        }
        else if ( !(o instanceof SingletonPredictionContext) ) {
            return false;
        }

        if ( this.hashCode() !== o.hashCode() ) {
            return false; // can't be same if hash is different
        }

        var s = o
        return returnState === s.returnState &&
            (parent!=null && parent.equals(s.parent));
    }
});

function EmptyPredictionContext(){
    SingletonPredictionContext.call(this, null, this.EMPTY_RETURN_STATE);
}
EmptyPredictionContext.prototype = _.create(SingletonPredictionContext.prototype,{
    isEmpty:function(){ return true; },
    size:function() {
        return 1;
    },
    getReturnState:function(index){
        return this.returnState;
    }
});
PredictionContext.EMPTY = new EmptyPredictionContext();

/*
 @param a SingletonPredictionContext
 */
function ArrayPredictionContext(parents, returnStates){
    if(arguments.length === 1){
        var a = arguments[0];
        return ArrayPredictionContext([a.parent], [a.returnState]);
    }
    PredictionContext.call(this, PredictionContext.calculateHashCode(parents, returnStates));
    if(parents!=null && parents.length>0)
        throw new Error();

    if(returnStates!=null && returnStates.length>0)
        throw new Error();
//	System.err.println("CREATE ARRAY: "+Arrays.toString(parents)+", "+Arrays.toString(returnStates));
    this.parents = parents;
    this.returnStates = returnStates;
}

ArrayPredictionContext.prototype = _.create(PredictionContext.prototype, {
    isEmpty:function(){
        return this.returnStates[0]=== PredictionContext.EMPTY_RETURN_STATE;
    },
    size:function() {
        return this.returnStates.length;
    },
    getParent:function(index){
        return this.parents[index];
    },
    getReturnState:function(index){
        return this.returnStates[index];
    },

    equals:function(o){
        if (this == o) {
            return true;
        }
        else if ( !(o instanceof ArrayPredictionContext) ) {
            return false;
        }

        if ( this.hashCode() !== o.hashCode() ) {
            return false; // can't be same if hash is different
        }

        var a = o;
        return sutil.Arrays_equals(returnStates, a.returnStates) &&
            sutil.Arrays_equals(parents, a.parents);
    }
});