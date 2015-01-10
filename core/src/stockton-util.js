
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
