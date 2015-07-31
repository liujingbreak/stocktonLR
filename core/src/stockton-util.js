var _ = require("lodash");

var RangeUtil = {
	
	startsBeforeDisjoint:function(r1, r2){
		return r1.from<r2.from && r1.to<r2.from;
	},
	
	startsAfterDisjoint:function(r1, r2){
		return r1.from > r2.to;
	},
	
	union:function(r1, r2){
		return {
			from: r1.from < r2.from ? r1.from : r2.from,
			to: r1.to > r2.to ? r1.to : r2.to
		};
	},
	
	isOverlap:function(r1, r2){
		return !(this.startsBeforeDisjoint(r1, r2) || this.startsAfterDisjoint(r1, r2));
	},

	intersection:function(range1, range2){
		return {
			from: range1.from > range2.from ? range1.from: range2.from,
			to: range1.to < range2.to ? range1.to: range2.to
		};
	}
};

exports.RangeUtil = RangeUtil;

function DoubleKeyMap(){
	this.data = {};
}
DoubleKeyMap.prototype ={
	get:function(k1, k2){
		var data2 = this.data[k1.toString()];
		if ( data2==null ) return null;
		return data2[k2.toString()];
	},
	
	put: function(k1, k2, v){
		k1 = k1.toString();
		k2 = k2.toString();
		var data2 = this.data[k1];
		var prev = null;
		if ( data2==null ) {
			data2 = {};
			this.data[k1] = data2;
		}
		else {
			prev = data2[k2];
		}
		data2[k2] = v;
		return prev;
	}
};

Arrays_equals = function(a1, a2){
	if(a1.length == a2.length){
		return a1.every(function(e1, i){
			return e1 == a2[i];
		});
	}
	return false;
};

_.extend(exports, {
	DoubleKeyMap:DoubleKeyMap,
	Arrays_equals: Arrays_equals
});



