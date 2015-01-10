var util = require('util');
function uuid(obj){
	return typeof(obj) == 'string'? obj: (obj._uuid != null? obj._uuid : obj.uuid());
}

var Utils={
	capitalize:function(s){
		return s.charAt(0).toUpperCase() + s.substring(1);
	},
	decapitalize:function(s){
		return s.charAt(0).toLowerCase() + s.substring(1);
	},
	setSize:function(list, size){
		if(size < list.length){
			for(var i=size,l=list.length; i<l; i++)
				list[i] = null;
		}else {
			while (size > list.length) {
				list.push(null);
			}
		}
	}
};
exports.Utils = Utils;

exports.Graph = (function(){
	function Graph(){
		this.nodes = {};
	}
	function Node(payload){
		this.payload = payload;
	}
	Node.prototype={
		toString:function() { return this.payload.toString(); },
		addEdge:function(n) {
            if ( this.edges==null ){
            	this.edges = [];
            }
            if ( edges.indexOf(n) == -1 ) edges.push(n);
        }
	};
	Graph.prototype ={
		/**
		a, b must be string or have uuid() function
		*/
		addEdge:function( a,  b) {
			var a_node = this.getNode(a);
			var b_node = this.getNode(b);
			a_node.addEdge(b_node);
		},
		getNode:function( a) {
			var existing = this.nodes[uuid(a)];
			if ( existing!=null ) return existing;
			var n = new Node(a);
			this.nodes[uuid(a)] = n;
			return n;
		},
		sort:function() {
			var visited = new OrderedHashSet();
			var sorted = [];
			while ( visited.size() < this.nodes.length ) {
				// pick any unvisited node, n
				var n = null;
				for( id in this.nodes){
					if(!this.nodes.hasOwnProperty(id))
						continue;
				//for (Iterator it = nodes.values().iterator(); it.hasNext();) {
					n = this.nodes[id];
					if ( !visited.contains(n) ) break;
				}
				this.DFS(n, visited, sorted);
			}
			return sorted;
		},
		DFS:function(n, visited, sorted) {
			if ( visited.contains(n) ) return;
			visited.add(n);
			if ( n.edges!=null ) {
				for(var i=0,l=n.edges.length; i<l; i++){
					var target = n.edges[i];
					this.DFS(target, visited, sorted);
				}
			}
			sorted.push(n.payload);
		}
	};
	return Graph;
})();

exports.MultiMap = (function(){
	function MultiMap(){
		this.obj ={};
	}
	MultiMap.prototype ={
		map:function(key,value){
			var elementsForKey = this.obj[key];
			if ( elementsForKey==null ) {
				elementsForKey = [];
				this.obj[key] = elementsForKey;
			}
			elementsForKey.push(value);
		},
		getPairs:function(){
			var pairs =[];
			for(key in this.obj){
				if(this.obj.hasOwnProperty(key))
					pairs.push({a:key, b:this.obj[key]});
			}
			return pairs;
		},
		values:function(){
			var v = [];
			for(k in this.obj)
				if(this.obj.hasOwnProperty(key))
					v.push(this.obj[k]);
			return v;
		},
		keySet:function(){
			return this.obj;
		}
	};
	return MultiMap;
})();

//-- runtime misc
(function(){
	var INTERVAL_POOL_MAX_VALUE=1000;
	var cache = new Array(INTERVAL_POOL_MAX_VALUE + 1);
	function Interval(a, b){
		this.a=a; this.b=b;
	}
	Interval.of = function(a, b) {
		// cache just a..a
		if ( a!=b || a<0 || a>INTERVAL_POOL_MAX_VALUE ) {
			return new Interval(a,b);
		}
		if ( cache[a]==null ) {
			cache[a] = new Interval(a,a);
		}
		return cache[a];
	}
	Interval.prototype={
		length:function() {
			if ( b<a ) return 0;
			return b-a+1;
		},
		equals:function(o) {
			if ( o==null || !(o instanceof Interval) ) {
				return false;
			}
			return this.a==o.a && this.b==o.b;
		},
		hashCode:function() {
			var hash = 23;
			hash = hash * 31 + this.a;
			hash = hash * 31 + this.b;
			return hash;
		},
		startsBeforeDisjoint:function(other) {
			return this.a<other.a && this.b<other.a;
		},
		startsBeforeNonDisjoint:function( other) {
			return this.a<=other.a && this.b>=other.a;
		},
		startsAfter:function(other) { return this.a>other.a; },
	
		startsAfterDisjoint:function( other) {
			return this.a>other.b;
		},
		startsAfterNonDisjoint:function( other) {
			return this.a>other.a && this.a<=other.b; 
		},
		union:function(other) {
			return Interval.of(Math.min(a, other.a), Math.max(b, other.b));
		},
		disjoint:function(other) {
			return this.startsBeforeDisjoint(other) || this.startsAfterDisjoint(other);
		},
		adjacent:function( other) {
			return this.a == other.b+1 || this.b == other.a-1;
		},
		properlyContains:function(other) {
			return other.a >= this.a && other.b <= this.b;
		},
		intersection:function(other) {
			return Interval.of(Math.max(a, other.a), Math.min(b, other.b));
		},
		toString:function() {
			return this.a +".."+ this.b;
		}
	};
	var INVALID = new Interval(-1,-2);
	
	function IntervalSet(intervals){
		this.readonly = false;
		if(arguments.length == 0){
			this.intervals = [];
		}else if(arguments.length == 1 && util.isArray(intervals)){
			this.intervals = intervals;
		}else{
			this.intervals = [];
			for(var i=0,l=arguments.length;i<l;i++){
				this.add(arguments[i]);
			}
		}
	}
	IntervalSet.of=function(a, b){
		var s = new IntervalSet();
		if(b == null)
			s.add(a);
		else
			s.add(a, b);
		return s;
	};
	IntervalSet.prototype={
		add:function(el, el2) {
			if ( this.readonly ) throw new Error("can't alter readonly IntervalSet");
			if(el2 === undefined){
				this._add(Interval.of(el, el));
			}else{
				this._add(Interval.of(el, el2));
			}
        },
        _add:function(addition){
        	if ( addition.b<addition.a ) {
				return;
			}
			// find position in list
			// Use iterators as we modify list in place
			var intervals = this.intervals;
			for(var i=0; i<intervals.length; i++){
				var r = intervals[i];
				if ( addition.equals(r) ) {
					return;
				}
				if ( addition.adjacent(r) || !addition.disjoint(r) ) {
					// next to each other, make a single larger interval
					var bigger = addition.union(r);
					intervals[i] = bigger;
					// make sure we didn't just create an interval that
					// should be merged with next interval in list
					while ( i+1 < intervals.length ) {
						var next = intervals[++i];
						if ( !bigger.adjacent(next) && bigger.disjoint(next) ) {
							break;
						}
						
						// if we bump up against or overlap next, merge
						intervals.splice(i, 1);  // remove this one
						i--;// move backwards to what we just set
						intervals[i] = bigger.union(next);// set to 3 merged ones
						// first call to next after previous duplicates the result
					}
					return;
				}
				if ( addition.startsBeforeDisjoint(r) ) {
					// insert before r
					i--;
					intervals.splice(i, 0, addition);
					return;
				}
				// if disjoint and after r, a future iteration will handle it
			}
			// ok, must be after last interval (and disjoint from last interval)
			// just add it
			intervals.push(addition);
        },
        addAll:function( set) {
			if ( set==null ) {
				return this;
			}
			if ( !(set instanceof IntervalSet) ) {
				throw new Error("can't add non IntSet ("+ set + ") to IntervalSet");
			}
			var other = set;
			// walk set and add each interval
			var n = other.intervals.length;
			for (var i = 0; i < n; i++) {
				var I = other.intervals[i];
				this.add(I.a,I.b);
			}
			return this;
		},
        contains:function(el) {
			var n = this.intervals.length;
			for (var i = 0; i < n; i++) {
				var I = this.intervals[i];
				var a = I.a;
				var b = I.b;
				if ( el<a ) {
					break; // list is sorted and el is before this interval; not here
				}
				if ( el>=a && el<=b ) {
					return true; // found in this interval
				}
			}
			return false;
		},
		isNil:function() {
			return this.intervals==null || this.intervals.length === 0;
		},
		remove:function( el) {
			if ( this.readonly ) throw new Error("can't alter readonly IntervalSet");
			var n = this.intervals.length;
			for (var i = 0; i < n; i++) {
				var I = this.intervals[i];
				var a = I.a;
				var b = I.b;
				if ( el<a ) {
					break; // list is sorted and el is before this interval; not here
				}
				// if whole interval x..x, rm
				if ( el==a && el==b ) {
					this.intervals.splice(i, 1);
					break;
				}
				// if on left edge x..b, adjust left
				if ( el==a ) {
					I.a++;
					break;
				}
				// if on right edge a..x, adjust right
				if ( el==b ) {
					I.b--;
					break;
				}
				// if in middle a..x..b, split interval
				if ( el>a && el<b ) { // found in this interval
					var oldb = I.b;
					I.b = el-1;      // [a..x-1]
					this.add(el+1, oldb); // add [x+1..b]
				}
			}
		},
		isReadonly:function() {
			return this.readonly;
		},
		setReadonly:function(readonly) {
			this.readonly = readonly;
		},
		size: function(){
			var n = 0;
			var numIntervals = this.intervals.length;
			if ( numIntervals==1 ) {
				var firstInterval = this.intervals[0];
				return firstInterval.b-firstInterval.a+1;
			}
			for (var i = 0; i < numIntervals; i++) {
				var I = this.intervals[i];
				n += (I.b-I.a+1);
			}
			return n;
		},
		getMinElement: function() {
			if ( this.isNil() ) {
				return 0;
			}
			var n = this.intervals.length;
			for (var i = 0; i < n; i++) {
				var I = this.intervals[i];
				var a = I.a;
				var b = I.b;
				for (var v=a; v<=b; v++) {
					if ( v>=0 ) return v;
				}
			}
			return 0;
		},
		getMaxElement:function(){
			if ( this.isNil() ) {
				return 0;
			}
			var last = this.intervals[this.intervals.length-1];
			return last.b;
		},
		
		complement:function(vocabularyIS){
			if(arguments.length === 2)
				return this.complement(IntervalSet.of(arguments[0], arguments[1]));
			
			if ( vocabularyIS==null ) {
            return null; // nothing in common with null set
			}
			if ( !(vocabularyIS instanceof IntervalSet ) ) {
				throw new Error("can't complement with non IntervalSet ("+
												   vocabularyIS+")");
			}
			var maxElement = vocabularyIS.getMaxElement();
	
			var compl = new IntervalSet();
			var n = this.intervals.length;
			if ( n ==0 ) {
				return compl;
			}
			var first = this.intervals[0];
			// add a range from 0 to first.a constrained to vocab
			if ( first.a > 0 ) {
				var s = IntervalSet.of(0, first.a-1);
				var a = s.and(vocabularyIS);
				compl.addAll(a);
			}
			for (var i=1; i<n; i++) { // from 2nd interval .. nth
				var previous = this.intervals[i-1];
				var current = this.intervals[i];
				var s = IntervalSet.of(previous.b+1, current.a-1);
				var a = s.and(vocabularyIS);
				compl.addAll(a);
			}
			var last = this.intervals[n -1];
			// add a range from last.b to maxElement constrained to vocab
			if ( last.b < maxElement ) {
				var s = IntervalSet.of(last.b+1, maxElement);
				var a = s.and(vocabularyIS);
				compl.addAll(a);
			}
			return compl;
		},
		
		and:function(other){
			if ( other==null ) { //|| !(other instanceof IntervalSet) ) {
				return null; // nothing in common with null set
			}
	
			var myIntervals = this.intervals;
			var theirIntervals = other.intervals;
			var intersection = null;
			var mySize = myIntervals.length;
			var theirSize = theirIntervals.length;
			var i = 0;
			var j = 0;
			// iterate down both interval lists looking for nondisjoint intervals
			while ( i<mySize && j<theirSize ) {
				var mine = myIntervals[i];
				var theirs = theirIntervals[j];
				//System.out.println("mine="+mine+" and theirs="+theirs);
				if ( mine.startsBeforeDisjoint(theirs) ) {
					// move this iterator looking for interval that might overlap
					i++;
				}
				else if ( theirs.startsBeforeDisjoint(mine) ) {
					// move other iterator looking for interval that might overlap
					j++;
				}
				else if ( mine.properlyContains(theirs) ) {
					// overlap, add intersection, get next theirs
					if ( intersection==null ) {
						intersection = new IntervalSet();
					}
					intersection.add(mine.intersection(theirs));
					j++;
				}
				else if ( theirs.properlyContains(mine) ) {
					// overlap, add intersection, get next mine
					if ( intersection==null ) {
						intersection = new IntervalSet();
					}
					intersection.add(mine.intersection(theirs));
					i++;
				}
				else if ( !mine.disjoint(theirs) ) {
					// overlap, add intersection
					if ( intersection==null ) {
						intersection = new IntervalSet();
					}
					intersection.add(mine.intersection(theirs));
					// Move the iterator of lower range [a..b], but not
					// the upper range as it may contain elements that will collide
					// with the next iterator. So, if mine=[0..115] and
					// theirs=[115..200], then intersection is 115 and move mine
					// but not theirs as theirs may collide with the next range
					// in thisIter.
					// move both iterators to next ranges
					if ( mine.startsAfterNonDisjoint(theirs) ) {
						j++;
					}
					else if ( theirs.startsAfterNonDisjoint(mine) ) {
						i++;
					}
				}
			}
			if ( intersection==null ) {
				return new IntervalSet();
			}
			return intersection;
		}
    };
	exports.IntervalSet = IntervalSet;
	exports.Interval = Interval;
})();

(function(){
	var BITS = 32;    // number of bits / int
    var LOG_BITS = 5; // 2^5 = 32
    var MOD_MASK = BITS - 1;
	function BitSet(bits_){
		if(bits_ == null)
			bits_ = BITS;
		if(typeof bits_ == 'number'){
			this.bits = new Array(((bits_ - 1) >> LOG_BITS) + 1);
		}else{
			this.bits = bits_;
		}
	}
	BitSet.of = function(el, el2, el3, el4) {
		switch(arguments.length){
		case 1:
			var s = new BitSet(el + 1);
			s.add(el);
			return s;
		case 2:
			var s = new BitSet(Math.max(el, el2)+1);
			s.add(el);
			s.add(el2);
			return s;
		default:
			var s = new BitSet();
			for(var i=0,l=arguments.length; i<l;i++)
				s.add(arguments[i]);
			return s;
		}
	}
	BitSet.prototype={
		or:function(a) {
			throw new Error('not supported');
		},
		size:function() {
			var deg = 0;
			for (var i = this.bits.length - 1; i >= 0; i--) {
				var word = this.bits[i];
				if (word !== 0) {
					for (var bit = BITS - 1; bit >= 0; bit--) {
						if ((word & (1 << bit)) != 0) {
							deg++;
						}
					}
				}
			}
			return deg;
		},
		add:function(el) {
			var n = el >> LOG_BITS;
			if (n >= this.bits.length) {
				this.growToInclude(el);
			}
			this.bits[n] |= this.bitMask(el);
		},
		numWordsToHold:function(el) {
			return (el >> LOG_BITS) + 1;
		},
		growToInclude:function(bit){
			var newSize = Math.max(this.bits.length << 1, this.numWordsToHold(bit));
			while(this.bits.length < newSize)
				this.bits.push(0);
		},
		bitMask:function(bitNumber) {
			var bitPosition = bitNumber & MOD_MASK; // bitNumber mod BITS
			return 1 << bitPosition;
		},
		member:function(el) {
			if ( el<0 ) {
				return false;
			}
			var n = el >> LOG_BITS;
			if (n >= this.bits.length) return false;
			return (this.bits[n] & this.bitMask(el)) != 0;
		}
	};
	exports.BitSet = BitSet;
})();

function MurmurHash(){
}
MurmurHash.DEFAULT_SEED = 0;
MurmurHash.initialize = function(seed){
	if(seed === undefined){
		return initialize(MurmurHash.DEFAULT_SEED);
	}
	return seed;
}
MurmurHash.update = function( hash, value) {
	if(typeof(value) == 'object')
		value = value != null ? value.hashCode() : 0;
	var c1 = 0xCC9E2D51;
	var c2 = 0x1B873593;
	var r1 = 15;
	var r2 = 13;
	var m = 5;
	var n = 0xE6546B64;

	var k = value;
	k = k * c1;
	k = (k << r1) | (k >>> (32 - r1));
	k = k * c2;

	hash = hash ^ k;
	hash = (hash << r2) | (hash >>> (32 - r2));
	hash = hash * m + n;

	return hash;
};

MurmurHash.finish = function( hash,  numberOfWords) {
	hash = hash ^ (numberOfWords * 4);
	hash = hash ^ (hash >>> 16);
	hash = hash * 0x85EBCA6B;
	hash = hash ^ (hash >>> 13);
	hash = hash * 0xC2B2AE35;
	hash = hash ^ (hash >>> 16);
	return hash;
};
MurmurHash.prototype = {
	hashCode:function( data, seed) {
		var hash = MurmurHash.initialize(seed);
		for (var i=0,l=data.length; i<l; i++) {
			var value = data[i];
			hash = MurmurHash.update(hash, value);
		}

		hash = MurmurHash.finish(hash, data.length);
		return hash;
	}
};
exports.MurmurHash = MurmurHash;

(function(){
function SimpleHashMap(){
	this.table = {};
	this.length = 0;
}
exports.HashMap = SimpleHashMap;
//var __opts = Object.prototype.toString;
//function isArray(){
//	return __opts.apply(o) == '[object Array]’;
//}
SimpleHashMap.prototype={
	put:function(key, value){
		var hashStr = this.hash(key);
		var entry = this.table[hashStr];
		if(entry){
			do{
				if( (key == null && entry.k == null) || key.equals(entry.k)){
					var v = entry.v;
					entry.v = value;
					return v;
				}
				var prev = entry;
				entry = entry.next;
				
			}while(entry != null);
			prev.next = {k: key, v: value};
			this.length++;
			return null;
		}else{
			this.table[hashStr] = {k: key, v: value};
			this.length++;
			return null;
		}
	},
	get:function(key){
		var hashStr = this.hash(key);
		var entry = this.table[hashStr];
		if(entry){
			do{
				if( (key == null && entry.k == null) || key.equals(entry.k)){
					return entry.v;
				}
				var prev = entry;
				entry = entry.next;
				
			}while(entry != null);
			return null;
		}
		return null;
	},
	containsKey:function(o){
		return this.get(o) != null;
	},
	remove:function(o){
		var hashStr = this.hash(o);
		var entry = this.table[hashStr], prev = null;
		if(entry){
			do{
				if( (o == null && entry.k == null) || o.equals(entry.k)){
					if(prev == null){
						if(entry.next)
							this.table[hashStr] = entry.next;
						else
							delete this.table[hashStr];
					}else{
						prev.next = entry.next;
					}
					this.length--;
					return entry.v;
				}
				prev = entry;
				entry = entry.next;
				
			}while(entry != null);
			return null;
		}
		return null;
	},
	clear:function(){
		this.table = {};
		this.length = 0;
	},
	size:function(){
		return this.length;
		
	},
	hash:function(o){
		if(o == null)
			return 'null';
		else if(o.hashCode)
			return o.hashCode() + '';
		else
			throw new Error('HashMap only allow key object with hashCode() method');
	}
};

})();
/**
Java like Hashmap
*/
(function(){
	MAXIMUM_CAPACITY = 1<<30;
	DEFAULT_INITIAL_CAPACITY = 1 << 4;
	DEFAULT_LOAD_FACTOR = 0.75;
	EMPTY_TABLE = [];
	
function HashMap(){
	this.table = [];
	this.size = 0;
	this.modCount = 0;
	this.loadFactor = DEFAULT_LOAD_FACTOR;
	this.threshold = DEFAULT_INITIAL_CAPACITY;
}
var Integer = {};
Integer.highestOneBit = function( i) {
        // HD, Figure 3-1
        i |= (i >>  1);
        i |= (i >>  2);
        i |= (i >>  4);
        i |= (i >>  8);
        i |= (i >> 16);
        return i - (i >>> 1);
};

Integer.bitCount = function(i) {
        // HD, Figure 5-2
        i = i - ((i >>> 1) & 0x55555555);
        i = (i & 0x33333333) + ((i >>> 2) & 0x33333333);
        i = (i + (i >>> 4)) & 0x0f0f0f0f;
        i = i + (i >>> 8);
        i = i + (i >>> 16);
        return i & 0x3f;
}
HashMap.prototype = {
	put:function(key, value){
		if (this.table.length == 0) {
            this.inflateTable(this.threshold);
        }
		if (key == null)
            return this.putForNullKey(value);
        var hash = hash(key);
        var i = indexFor(hash, table.length);
        for (e = table[i]; e != null; e = e.next) {
            var k;
            if (e.hash == hash && ((k = e.key) == key || key.equals(k))) {
                var oldValue = e.value;
                e.value = value;
                e.recordAccess(this);
                return oldValue;
            }
        }

        this.modCount++;
        addEntry(hash, key, value, i);
        return null;
	},
	putForNullKey:function(value) {
		if(this.table.length > 0)
			for (var e = this.table[0]; e != null; e = e.next) {
				if (e.key == null) {
					var oldValue = e.value;
					e.value = value;
					//e.recordAccess(this);
					return oldValue;
				}
			}
        this.modCount++;
        this.addEntry(0, null, value, 0);
        return null;
    },
    addEntry:function( hash, key, value, bucketIndex) {
        if ((size >= threshold) && (null != this.table[bucketIndex])) {
            resize(2 * table.length);
            hash = (null != key) ? this.hash(key) : 0;
            bucketIndex = indexFor(hash, this.table.length);
        }

        this.createEntry(hash, key, value, bucketIndex);
    },
    createEntry:function(hash, key, value, bucketIndex) {
        var e = table[bucketIndex];
        table[bucketIndex] = new Entry(hash, key, value, e);
        size++;
    },
    inflateTable:function(toSize){
    	var capacity = this._roundUpToPowerOf2(toSize);
    	threshold = Math.floor(Math.min(capacity * this.loadFactor, MAXIMUM_CAPACITY + 1));
        while(this.table.length < capacity)
        	this.table.push(null);
        //todo: initHashSeedAsNeeded(capacity);
    },
    _roundUpToPowerOf2:function( number) {
        // assert number >= 0 : "number must be non-negative";
        var rounded = number >= MAXIMUM_CAPACITY ? MAXIMUM_CAPACITY
                : (rounded = Integer.highestOneBit(number)) != 0
                    ? (Integer.bitCount(number) > 1) ? rounded << 1 : rounded
                    : 1;
        
        return rounded;
    }
};

//exports.HashMap = HashMap;
})();
