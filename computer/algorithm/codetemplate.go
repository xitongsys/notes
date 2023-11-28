package main

import (
	"bufio"
	"fmt"
	"os"
)

// math //////////////////////

type NumInt interface {
	int8 | int16 | int32 | int64 | int |
		uint8 | uint16 | uint32 | uint64 | uint
}

type NumFloat interface {
	float32 | float64
}

type Ordered interface {
	NumInt | NumFloat | ~string
}

func abs[T NumInt | NumFloat](a T) T {
	if a < 0 {
		return -a
	}
	return a
}

func sum[T NumInt | NumFloat | string](vs ...T) T {
	r := vs[0]
	for i := 1; i < len(vs); i++ {
		r += vs[i]
	}
	return r
}

func max[T NumInt | NumFloat | string](vs ...T) T {
	r := vs[0]
	for i := 1; i < len(vs); i++ {
		if vs[i] > r {
			r = vs[i]
		}
	}
	return r
}

func min[T NumInt | NumFloat | string](vs ...T) T {
	r := vs[0]
	for i := 1; i < len(vs); i++ {
		if vs[i] < r {
			r = vs[i]
		}
	}
	return r
}

func gcd[T NumInt](a, b T) T {
	if a == T(0) {
		return b
	}
	return gcd(b%a, a)
}

func mpow[T NumInt](a, n, mod T) T {
	if n == 0 {
		return 1
	}
	r := mpow(a, n/2, mod)
	r = (r * r) % mod
	if n%2 == 1 {
		r *= a
	}
	return r % mod
}

func inv[T NumInt](a, mod T) T {
	return mpow(a%mod, mod-2, mod)
}

func bit_one_cnt[T NumInt](a T) int {
	r := 0
	for a > 0 {
		r += int(a & 1)
		a >>= 1
	}
	return r
}

func lower_bound[T NumInt | NumFloat | string](vs []T, t T) int {
	if len(vs) == 0 {
		return -1
	}
	l, r := 0, len(vs)-1
	for l <= r {
		m := l + (r-l)/2
		if vs[m] < t {
			l = m + 1
		} else {
			r = m - 1
		}
	}

	if l < len(vs) {
		return l
	}

	return -1
}

func upper_bound[T NumInt | NumFloat | string](vs []T, t T) int {
	i := lower_bound(vs, t)
	if i < 0 {
		return i
	}

	if vs[i] == t {
		i++
	}

	if i < len(vs) {
		return i
	}
	return -1
}

// HashSet ///////////

type HashSet[T comparable] struct {
	mp map[T]int
}

func NewHashSet[T comparable]() *HashSet[T] {
	res := &HashSet[T]{
		mp: map[T]int{},
	}
	return res
}

func (hs *HashSet[T]) Insert(v T) {
	if _, ok := hs.mp[v]; !ok {
		hs.mp[v] = 1
	}
}

func (hs *HashSet[T]) Del(v T) {
	if _, ok := hs.mp[v]; ok {
		delete(hs.mp, v)
	}
}

func (hs *HashSet[T]) Size() int {
	return len(hs.mp)
}

func (hs *HashSet[T]) Contains(v T) bool {
	_, ok := hs.mp[v]
	return ok
}

// MultiHashSet /////////

type MultiHashSet[T comparable] struct {
	mp   map[T]int
	size int
}

func NewMultiHashSet[T comparable]() *HashSet[T] {
	res := &HashSet[T]{
		mp: map[T]int{},
	}
	return res
}

func (hs *MultiHashSet[T]) Insert(v T) {
	if _, ok := hs.mp[v]; !ok {
		hs.mp[v] = 0
	}
	hs.mp[v]++
	hs.size++
}

func (hs *MultiHashSet[T]) Del(v T) {
	if _, ok := hs.mp[v]; ok {
		hs.mp[v]--
		if hs.mp[v] == 0 {
			delete(hs.mp, v)
		}
		hs.size--
	}
}

func (hs *MultiHashSet[T]) DelAll(v T) {
	if _, ok := hs.mp[v]; ok {
		hs.size -= hs.mp[v]
		delete(hs.mp, v)
	}
}

func (hs *MultiHashSet[T]) Size() int {
	return hs.size
}

func (hs *MultiHashSet[T]) Contains(v T) bool {
	_, ok := hs.mp[v]
	return ok
}

func (hs *MultiHashSet[T]) Count(v T) int {
	if _, ok := hs.mp[v]; ok {
		return hs.mp[v]
	}
	return 0
}

// TreeMap ///////////

type TreeMap[Key, Value any] struct {
	endNode    *node[Key, Value]
	beginNode  *node[Key, Value]
	count      int
	keyCompare func(a Key, b Key) bool
}

type node[Key, Value any] struct {
	right   *node[Key, Value]
	left    *node[Key, Value]
	parent  *node[Key, Value]
	isBlack bool
	key     Key
	value   Value
}

// New creates and returns new TreeMap.
func NewTreeMap[Key Ordered, Value any]() *TreeMap[Key, Value] {
	endNode := &node[Key, Value]{isBlack: true}
	return &TreeMap[Key, Value]{beginNode: endNode, endNode: endNode, keyCompare: defaultKeyCompare[Key]}
}

// NewWithKeyCompare creates and returns new TreeMap with the specified key compare function.
// Parameter keyCompare is a function returning a < b.
func NewWithKeyCompare[Key, Value any](
	keyCompare func(a, b Key) bool,
) *TreeMap[Key, Value] {
	endNode := &node[Key, Value]{isBlack: true}
	return &TreeMap[Key, Value]{beginNode: endNode, endNode: endNode, keyCompare: keyCompare}
}

// Len returns total count of elements in a map.
// Complexity: O(1).
func (t *TreeMap[Key, Value]) Len() int { return t.count }

// Set sets the value and silently overrides previous value if it exists.
// Complexity: O(log N).
func (t *TreeMap[Key, Value]) Set(key Key, value Value) {
	parent := t.endNode
	current := parent.left
	less := true
	for current != nil {
		parent = current
		switch {
		case t.keyCompare(key, current.key):
			current = current.left
			less = true
		case t.keyCompare(current.key, key):
			current = current.right
			less = false
		default:
			current.value = value
			return
		}
	}
	x := &node[Key, Value]{parent: parent, value: value, key: key}
	if less {
		parent.left = x
	} else {
		parent.right = x
	}
	if t.beginNode.left != nil {
		t.beginNode = t.beginNode.left
	}
	t.insertFixup(x)
	t.count++
}

// Del deletes the value.
// Complexity: O(log N).
func (t *TreeMap[Key, Value]) Del(key Key) {
	z := t.findNode(key)
	if z == nil {
		return
	}
	if t.beginNode == z {
		if z.right != nil {
			t.beginNode = z.right
		} else {
			t.beginNode = z.parent
		}
	}
	t.count--
	removeNode(t.endNode.left, z)
}

// Clear clears the map.
// Complexity: O(1).
func (t *TreeMap[Key, Value]) Clear() {
	t.count = 0
	t.beginNode = t.endNode
	t.endNode.left = nil
}

// Get retrieves a value from a map for specified key and reports if it exists.
// Complexity: O(log N).
func (t *TreeMap[Key, Value]) Get(id Key) (Value, bool) {
	node := t.findNode(id)
	if node == nil {
		node = t.endNode
	}
	return node.value, node != t.endNode
}

// Contains checks if key exists in a map.
// Complexity: O(log N)
func (t *TreeMap[Key, Value]) Contains(id Key) bool { return t.findNode(id) != nil }

// Range returns a pair of iterators that you can use to go through all the keys in the range [from, to].
// More specifically it returns iterators pointing to lower bound and upper bound.
// Complexity: O(log N).
func (t *TreeMap[Key, Value]) Range(from, to Key) (ForwardIterator[Key, Value], ForwardIterator[Key, Value]) {
	return t.LowerBound(from), t.UpperBound(to)
}

// LowerBound returns an iterator pointing to the first element that is not less than the given key.
// Complexity: O(log N).
func (t *TreeMap[Key, Value]) LowerBound(key Key) ForwardIterator[Key, Value] {
	result := t.endNode
	node := t.endNode.left
	if node == nil {
		return ForwardIterator[Key, Value]{tree: t, node: t.endNode}
	}
	for {
		if t.keyCompare(node.key, key) {
			if node.right != nil {
				node = node.right
			} else {
				return ForwardIterator[Key, Value]{tree: t, node: result}
			}
		} else {
			result = node
			if node.left != nil {
				node = node.left
			} else {
				return ForwardIterator[Key, Value]{tree: t, node: result}
			}
		}
	}
}

// UpperBound returns an iterator pointing to the first element that is greater than the given key.
// Complexity: O(log N).
func (t *TreeMap[Key, Value]) UpperBound(key Key) ForwardIterator[Key, Value] {
	result := t.endNode
	node := t.endNode.left
	if node == nil {
		return ForwardIterator[Key, Value]{tree: t, node: t.endNode}
	}
	for {
		if !t.keyCompare(key, node.key) {
			if node.right != nil {
				node = node.right
			} else {
				return ForwardIterator[Key, Value]{tree: t, node: result}
			}
		} else {
			result = node
			if node.left != nil {
				node = node.left
			} else {
				return ForwardIterator[Key, Value]{tree: t, node: result}
			}
		}
	}
}

// Iterator returns an iterator for tree map.
// It starts at the first element and goes to the one-past-the-end position.
// You can iterate a map at O(N) complexity.
// Method complexity: O(1)
func (t *TreeMap[Key, Value]) Iterator() ForwardIterator[Key, Value] {
	return ForwardIterator[Key, Value]{tree: t, node: t.beginNode}
}

// Reverse returns a reverse iterator for tree map.
// It starts at the last element and goes to the one-before-the-start position.
// You can iterate a map at O(N) complexity.
// Method complexity: O(log N)
func (t *TreeMap[Key, Value]) Reverse() ReverseIterator[Key, Value] {
	node := t.endNode.left
	if node != nil {
		node = mostRight(node)
	}
	return ReverseIterator[Key, Value]{tree: t, node: node}
}

func defaultKeyCompare[Key Ordered](
	a, b Key,
) bool {
	return a < b
}

func (t *TreeMap[Key, Value]) findNode(id Key) *node[Key, Value] {
	current := t.endNode.left
	for current != nil {
		switch {
		case t.keyCompare(id, current.key):
			current = current.left
		case t.keyCompare(current.key, id):
			current = current.right
		default:
			return current
		}
	}
	return nil
}

func mostLeft[Key, Value any](
	x *node[Key, Value],
) *node[Key, Value] {
	for x.left != nil {
		x = x.left
	}
	return x
}

func mostRight[Key, Value any](
	x *node[Key, Value],
) *node[Key, Value] {
	for x.right != nil {
		x = x.right
	}
	return x
}

func successor[Key, Value any](
	x *node[Key, Value],
) *node[Key, Value] {
	if x.right != nil {
		return mostLeft(x.right)
	}
	for x != x.parent.left {
		x = x.parent
	}
	return x.parent
}

func predecessor[Key, Value any](
	x *node[Key, Value],
) *node[Key, Value] {
	if x.left != nil {
		return mostRight(x.left)
	}
	for x.parent != nil && x != x.parent.right {
		x = x.parent
	}
	return x.parent
}

func rotateLeft[Key, Value any](
	x *node[Key, Value],
) {
	y := x.right
	x.right = y.left
	if x.right != nil {
		x.right.parent = x
	}
	y.parent = x.parent
	if x == x.parent.left {
		x.parent.left = y
	} else {
		x.parent.right = y
	}
	y.left = x
	x.parent = y
}

func rotateRight[Key, Value any](
	x *node[Key, Value],
) {
	y := x.left
	x.left = y.right
	if x.left != nil {
		x.left.parent = x
	}
	y.parent = x.parent
	if x == x.parent.left {
		x.parent.left = y
	} else {
		x.parent.right = y
	}
	y.right = x
	x.parent = y
}

func (t *TreeMap[Key, Value]) insertFixup(x *node[Key, Value]) {
	root := t.endNode.left
	x.isBlack = x == root
	for x != root && !x.parent.isBlack {
		if x.parent == x.parent.parent.left {
			y := x.parent.parent.right
			if y != nil && !y.isBlack {
				x = x.parent
				x.isBlack = true
				x = x.parent
				x.isBlack = x == root
				y.isBlack = true
			} else {
				if x != x.parent.left {
					x = x.parent
					rotateLeft(x)
				}
				x = x.parent
				x.isBlack = true
				x = x.parent
				x.isBlack = false
				rotateRight(x)
				break
			}
		} else {
			y := x.parent.parent.left
			if y != nil && !y.isBlack {
				x = x.parent
				x.isBlack = true
				x = x.parent
				x.isBlack = x == root
				y.isBlack = true
			} else {
				if x == x.parent.left {
					x = x.parent
					rotateRight(x)
				}
				x = x.parent
				x.isBlack = true
				x = x.parent
				x.isBlack = false
				rotateLeft(x)
				break
			}
		}
	}
}

//nolint:gocyclo
//noinspection GoNilness
func removeNode[Key, Value any](
	root, z *node[Key, Value],
) {
	var y *node[Key, Value]
	if z.left == nil || z.right == nil {
		y = z
	} else {
		y = successor(z)
	}
	var x *node[Key, Value]
	if y.left != nil {
		x = y.left
	} else {
		x = y.right
	}
	var w *node[Key, Value]
	if x != nil {
		x.parent = y.parent
	}
	if y == y.parent.left {
		y.parent.left = x
		if y != root {
			w = y.parent.right
		} else {
			root = x // w == nil
		}
	} else {
		y.parent.right = x
		w = y.parent.left
	}
	removedBlack := y.isBlack
	if y != z {
		y.parent = z.parent
		if z == z.parent.left {
			y.parent.left = y
		} else {
			y.parent.right = y
		}
		y.left = z.left
		y.left.parent = y
		y.right = z.right
		if y.right != nil {
			y.right.parent = y
		}
		y.isBlack = z.isBlack
		if root == z {
			root = y
		}
	}
	if removedBlack && root != nil {
		if x != nil {
			x.isBlack = true
		} else {
			for {
				if w != w.parent.left {
					if !w.isBlack {
						w.isBlack = true
						w.parent.isBlack = false
						rotateLeft(w.parent)
						if root == w.left {
							root = w
						}
						w = w.left.right
					}
					if (w.left == nil || w.left.isBlack) && (w.right == nil || w.right.isBlack) {
						w.isBlack = false
						x = w.parent
						if x == root || !x.isBlack {
							x.isBlack = true
							break
						}
						if x == x.parent.left {
							w = x.parent.right
						} else {
							w = x.parent.left
						}
					} else {
						if w.right == nil || w.right.isBlack {
							w.left.isBlack = true
							w.isBlack = false
							rotateRight(w)
							w = w.parent
						}
						w.isBlack = w.parent.isBlack
						w.parent.isBlack = true
						w.right.isBlack = true
						rotateLeft(w.parent)
						break
					}
				} else {
					if !w.isBlack {
						w.isBlack = true
						w.parent.isBlack = false
						rotateRight(w.parent)
						if root == w.right {
							root = w
						}
						w = w.right.left
					}
					if (w.left == nil || w.left.isBlack) && (w.right == nil || w.right.isBlack) {
						w.isBlack = false
						x = w.parent
						if !x.isBlack || x == root {
							x.isBlack = true
							break
						}
						if x == x.parent.left {
							w = x.parent.right
						} else {
							w = x.parent.left
						}
					} else {
						if w.left == nil || w.left.isBlack {
							w.right.isBlack = true
							w.isBlack = false
							rotateLeft(w)
							w = w.parent
						}
						w.isBlack = w.parent.isBlack
						w.parent.isBlack = true
						w.left.isBlack = true
						rotateRight(w.parent)
						break
					}
				}
			}
		}
	}
}

// ForwardIterator represents a position in a tree map.
// It is designed to iterate a map in a forward order.
// It can point to any position from the first element to the one-past-the-end element.
type ForwardIterator[Key, Value any] struct {
	tree *TreeMap[Key, Value]
	node *node[Key, Value]
}

// Valid reports if the iterator position is valid.
// In other words it returns true if an iterator is not at the one-past-the-end position.
func (i ForwardIterator[Key, Value]) Valid() bool { return i.node != i.tree.endNode }

// Next moves an iterator to the next element.
// It panics if it goes out of bounds.
func (i *ForwardIterator[Key, Value]) Next() {
	if i.node == i.tree.endNode {
		panic("out of bound iteration")
	}
	i.node = successor(i.node)
}

// Prev moves an iterator to the previous element.
// It panics if it goes out of bounds.
func (i *ForwardIterator[Key, Value]) Prev() {
	i.node = predecessor(i.node)
	if i.node == nil {
		panic("out of bound iteration")
	}
}

// Key returns a key at the iterator position
func (i ForwardIterator[Key, Value]) Key() Key { return i.node.key }

// Value returns a value at the iterator position
func (i ForwardIterator[Key, Value]) Value() Value { return i.node.value }

// ReverseIterator represents a position in a tree map.
// It is designed to iterate a map in a reverse order.
// It can point to any position from the one-before-the-start element to the last element.
type ReverseIterator[Key, Value any] struct {
	tree *TreeMap[Key, Value]
	node *node[Key, Value]
}

// Valid reports if the iterator position is valid.
// In other words it returns true if an iterator is not at the one-before-the-start position.
func (i ReverseIterator[Key, Value]) Valid() bool { return i.node != nil }

// Next moves an iterator to the next element in reverse order.
// It panics if it goes out of bounds.
func (i *ReverseIterator[Key, Value]) Next() {
	if i.node == nil {
		panic("out of bound iteration")
	}
	i.node = predecessor(i.node)
}

// Prev moves an iterator to the previous element in reverse order.
// It panics if it goes out of bounds.
func (i *ReverseIterator[Key, Value]) Prev() {
	if i.node != nil {
		i.node = successor(i.node)
	} else {
		i.node = i.tree.beginNode
	}
	if i.node == i.tree.endNode {
		panic("out of bound iteration")
	}
}

// Key returns a key at the iterator position
func (i ReverseIterator[Key, Value]) Key() Key { return i.node.key }

// Value returns a value at the iterator position
func (i ReverseIterator[Key, Value]) Value() Value { return i.node.value }

// SegmentTree ///////////

type Node struct {
	lpos, rpos int64
	val, d     int64
}

type SegTree struct {
	nodes []Node
	op    func(int64, int64) int64
}

func NewSegTree(lpos, rpos int64, op func(int64, int64) int64) *SegTree {
	n := rpos - lpos + 1
	return &SegTree{
		nodes: make([]Node, 4*n+1),
		op:    op,
	}
}

func (st *SegTree) Init(u int64, lpos int64, rpos int64) {
	st.nodes[u].lpos = lpos
	st.nodes[u].rpos = rpos
	if lpos == rpos {
		return
	}
	mpos := lpos + (rpos-lpos)/2
	lu, ru := 2*u+1, 2*u+2
	if lu < int64(len(st.nodes)) {
		st.Init(lu, lpos, mpos)
	}
	if ru < int64(len(st.nodes)) {
		st.Init(2*u+2, mpos+1, rpos)
	}
}

func (st *SegTree) Pushdown(u int64) {
	if st.nodes[u].d == 0 {
		return
	}
	lu, ru := 2*u+1, 2*u+2
	if lu < int64(len(st.nodes)) {
		st.nodes[lu].val += st.nodes[u].d
		st.nodes[lu].d += st.nodes[u].d
	}
	if ru < int64(len(st.nodes)) {
		st.nodes[ru].val += st.nodes[u].d
		st.nodes[ru].d += st.nodes[u].d
	}
	st.nodes[u].d = 0
}

func (st *SegTree) Add(lpos, rpos, d, u int64) {
	if lpos == st.nodes[u].lpos && rpos == st.nodes[u].rpos {
		st.nodes[u].d += d
		st.nodes[u].val += d
		return
	}
	st.Pushdown(u)
	mpos := st.nodes[u].lpos + (st.nodes[u].rpos-st.nodes[u].lpos)/2
	lu, ru := 2*u+1, 2*u+2
	if rpos <= mpos {
		st.Add(lpos, rpos, d, lu)
	} else if lpos > mpos {
		st.Add(lpos, rpos, d, ru)
	} else {
		st.Add(lpos, mpos, d, lu)
		st.Add(mpos+1, rpos, d, lu)
	}

	st.nodes[u].val = st.op(st.nodes[lu].val, st.nodes[ru].val)
}

func (st *SegTree) Set(pos, val int64) {
	val_old := st.Query(pos, pos, 0)
	st.Add(pos, pos, val-val_old, 0)
}

func (st *SegTree) Query(lpos, rpos, u int64) int64 {
	if st.nodes[u].lpos == lpos && st.nodes[u].rpos == rpos {
		return st.nodes[u].val
	}
	st.Pushdown(u)

	mpos := st.nodes[u].lpos + (st.nodes[u].rpos-st.nodes[u].lpos)/2
	lu, ru := 2*u+1, 2*u+2
	if rpos <= mpos {
		return st.Query(lpos, rpos, lu)
	} else if lpos > mpos {
		return st.Query(lpos, rpos, ru)
	} else {
		return st.op(st.Query(lpos, mpos, lu), st.Query(mpos+1, rpos, ru))
	}
}

// TreeSet ///////////////

type TreeSet[T Ordered] struct {
	mp *TreeMap[T, int]
}

func NewTreeSet[T Ordered]() *TreeSet[T] {
	return &TreeSet[T]{
		mp: NewTreeMap[T, int](),
	}
}

func (ts *TreeSet[T]) Insert(v T) {
	ts.mp.Set(v, 1)
}

func (ts *TreeSet[T]) Del(v T) {
	ts.mp.Del(v)
}

func (ts *TreeSet[T]) Size() int {
	return ts.mp.Len()
}

func (ts *TreeSet[T]) Contains(v T) bool {
	return ts.Contains(v)
}

func (ts *TreeSet[T]) LowerBound(v T) ForwardIterator[T, int] {
	return ts.mp.LowerBound(v)
}

func (ts *TreeSet[T]) UpperBound(v T) ForwardIterator[T, int] {
	return ts.mp.UpperBound(v)
}

// MultiTreeSet ///////////

type MultiTreeSet[T Ordered] struct {
	mp   *TreeMap[T, int]
	size int
}

func NewMultiTreeSet[T Ordered]() *MultiTreeSet[T] {
	res := &MultiTreeSet[T]{
		mp:   NewTreeMap[T, int](),
		size: 0,
	}
	return res
}

func (ts *MultiTreeSet[T]) Insert(v T) {
	if !ts.mp.Contains(v) {
		ts.mp.Set(v, 0)
	}
	c, _ := ts.mp.Get(v)
	ts.mp.Set(v, c+1)
	ts.size++
}

func (ts *MultiTreeSet[T]) Del(v T) {
	if c, ok := ts.mp.Get(v); ok {
		if c == 1 {
			ts.mp.Del(v)
		} else {
			ts.mp.Set(v, c-1)
		}
		ts.size--
	}
}

func (ts *MultiTreeSet[T]) DelAll(v T) {
	if c, ok := ts.mp.Get(v); ok {
		ts.mp.Del(v)
		ts.size -= c
	}
}

func (ts *MultiTreeSet[T]) Size() int {
	return ts.size
}

func (ts *MultiTreeSet[T]) Contains(v T) bool {
	return ts.mp.Contains(v)
}

func (ts *MultiTreeSet[T]) Count(v T) int {
	if c, ok := ts.mp.Get(v); ok {
		return c
	}
	return 0
}

func (ts *MultiTreeSet[T]) LowerBound(v T) ForwardIterator[T, int] {
	return ts.mp.LowerBound(v)
}

func (ts *MultiTreeSet[T]) UpperBound(v T) ForwardIterator[T, int] {
	return ts.mp.UpperBound(v)
}

// DiffArray /////////////

type DiffArray[T NumInt] struct {
	n  int
	ds []T
}

func NewDiffArray[T NumInt](n int) *DiffArray[T] {
	return &DiffArray[T]{
		n:  n,
		ds: make([]T, n),
	}
}

func (df *DiffArray[T]) Add(b, e int, v T) {
	if b > e {
		return
	}
	df.ds[b] += v
	if e+1 < df.n {
		df.ds[e+1] -= v
	}
}

func (df *DiffArray[T]) Sum() []T {
	res := make([]T, df.n)
	for i := 0; i < df.n; i++ {
		res[i] = df.ds[i]
		if i > 0 {
			res[i] += res[i-1]
		}
	}
	return res
}

// RabinHash (Rolling Hash)

type RabinHash struct {
	h     int64
	mod   int64
	hashs []int64
	n     int
}

func NewRabinHash(s string) *RabinHash {
	h, mod := int64(101), int64(1e9+7)
	n := len(s)
	hashs := make([]int64, n)
	bs := []byte(s)
	hashs[0] = int64(bs[0])

	for i := 1; i < n; i++ {
		a := int64(bs[i])
		hashs[i] = ((hashs[i-1]*h)%mod + a) % mod
	}

	return &RabinHash{
		h:     h,
		mod:   mod,
		hashs: hashs,
		n:     n,
	}
}

func (rh *RabinHash) HashVal(b, e int) int64 {
	v := rh.hashs[e]
	if b > 0 {
		v2 := (rh.hashs[b-1] * mpow(rh.h, int64(e-b+1), rh.mod)) % rh.mod
		v -= v2
		v = (v%rh.mod + rh.mod) % rh.mod
	}
	return v
}

//////////////////////////////

/////////////////////////////////
func main() {
	in := bufio.NewReader(os.Stdin)
	out := bufio.NewWriter(os.Stdout)
	defer out.Flush()

	T := 0
	fmt.Fscan(in, &T)
}
