var RETURN_FALSE = function(){
    return false;
};

var TransitionMatches = {
    precedence: RETURN_FALSE,
    predicate: RETURN_FALSE,
    epsilon: RETURN_FALSE,
    action: RETURN_FALSE,
    atom:function(tran, symbol){
        return tran.label === symbol;
    },
    range:function(tran, symbol, minVocabSymbol, maxVocabSymbol) {
        return symbol >= tran.from && symbol <= tran.to;
    },
    rule: RETURN_FALSE,

    set:function(tran, symbol){
        return tran.set.contains(symbol);
    },

    notSet:function(tran, symbol, minVocabSymbol, maxVocabSymbol){
        return symbol >= minVocabSymbol && symbol <= maxVocabSymbol &&
            !TransitionMatches.set(tran, symbol, minVocabSymbol, maxVocabSymbol);
    },

    wildcard:function(tran, symbol, minVocabSymbol, maxVocabSymbol){
        return symbol >= minVocabSymbol && symbol <= maxVocabSymbol;
    }
};

Transition = {
    label:function(tran){
        switch(tran.type){
            case 'atom':
                return IntervalSet.of(tran.label);
            case 'range':
                return IntervalSet.of(tran.from, tran.to);
            case 'set':
                return tran.set;
            default:
                return null;
        }
    },

    matches:function(tran, moreArgs){
        return TransitionMatches[tran.type].apply(this, arguments);
    }
};

module.exports = Transition;
