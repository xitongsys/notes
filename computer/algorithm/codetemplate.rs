use std::cmp::Ordering;
use std::collections::binary_heap;
use std::collections::BTreeSet;
use std::collections::BinaryHeap;
use std::hash;
use std::io::{stdin, stdout, BufWriter, Write};
use std::num::NonZeroIsize;
use std::ptr;
use std::str::FromStr;
use std::{cmp, collections::HashSet};

use algo::Scanner;

mod algo {
    // segment tree //////////////
    #[derive(Clone)]
    struct SegTreeNode {
        lpos: i64,
        rpos: i64,
        val: i64,
        dval: i64,
    }

    pub struct SegTree {
        nodes: Vec<SegTreeNode>,
        op: fn(i64, i64) -> i64,
    }

    impl SegTree {
        pub fn max(a: i64, b: i64) -> i64 {
            return std::cmp::max(a, b);
        }

        pub fn min(a: i64, b: i64) -> i64 {
            return std::cmp::min(a, b);
        }

        pub fn sum(a: i64, b: i64) -> i64 {
            return a + b;
        }

        pub fn new(lpos: i64, rpos: i64, op: fn(i64, i64) -> i64) -> Self {
            let mut tree = SegTree {
                nodes: vec![
                    SegTreeNode {
                        lpos: 0,
                        rpos: 0,
                        val: 0,
                        dval: 0,
                    };
                    ((rpos - lpos + 1) * 4) as usize
                ],
                op: op,
            };

            tree.init(0, lpos, rpos);

            return tree;
        }

        pub fn init(&mut self, u: usize, lpos: i64, rpos: i64) {
            self.nodes[u].lpos = lpos;
            self.nodes[u].rpos = rpos;
            if lpos == rpos {
                return;
            }

            let mpos = lpos + (rpos - lpos) / 2;
            let lu = 2 * u + 1;
            let ru = 2 * u + 2;
            if lu < self.nodes.len() {
                self.init(lu, lpos, mpos);
            }
            if ru < self.nodes.len() {
                self.init(ru, mpos + 1, rpos);
            }
        }

        pub fn pushdown(&mut self, u: usize) {
            if self.nodes[u].dval == 0 {
                return;
            }

            let lu = 2 * u + 1;
            let ru = 2 * u + 2;

            if lu < self.nodes.len() {
                self.nodes[lu].val += self.nodes[u].dval;
                self.nodes[lu].dval += self.nodes[u].dval;
            }

            if ru < self.nodes.len() {
                self.nodes[ru].val += self.nodes[u].dval;
                self.nodes[ru].dval += self.nodes[u].dval;
            }
            self.nodes[u as usize].dval = 0;
        }

        pub fn add(&mut self, u: usize, lpos: i64, rpos: i64, d: i64) {
            if lpos == self.nodes[u].lpos && rpos == self.nodes[u].rpos {
                self.nodes[u].dval += d;
                self.nodes[u].val += d;
                return;
            }
            self.pushdown(u);
            let mpos = self.nodes[u].lpos + (self.nodes[u].rpos - self.nodes[u].lpos) / 2;
            let lu = (2 * u + 1);
            let ru = (2 * u + 2);
            if rpos <= mpos {
                self.add(lu, lpos, rpos, d);
            } else if lpos > mpos {
                self.add(ru, lpos, rpos, d);
            } else {
                self.add(lu, lpos, mpos, d);
                self.add(lu, mpos + 1, rpos, d);
            }

            self.nodes[u].val = (self.op)(self.nodes[lu].val, self.nodes[ru].val);
        }

        pub fn set(&mut self, pos: i64, val: i64) {
            let val_old = self.query(0, pos, pos);
            self.add(0, pos, pos, val - val_old);
        }

        pub fn query(&mut self, u: usize, lpos: i64, rpos: i64) -> i64 {
            if self.nodes[u].lpos == lpos && self.nodes[u].rpos == rpos {
                return self.nodes[u].val;
            }
            self.pushdown(u);

            let mpos = self.nodes[u].lpos + (self.nodes[u].rpos - self.nodes[u].lpos) / 2;
            let lu = 2 * u + 1;
            let ru = 2 * u + 2;
            if rpos <= mpos {
                return self.query(lu, lpos, rpos);
            } else if lpos > mpos {
                return self.query(ru, lpos, rpos);
            } else {
                return (self.op)(self.query(lu, lpos, mpos), self.query(ru, mpos + 1, rpos));
            }
        }
    }

    // DiffArray ////////////
    pub struct DiffArray<T: Clone + Copy + std::ops::Add<Output = T> + std::ops::Sub<Output = T>> {
        n: usize,
        ds: Vec<T>,
    }

    impl<T: Clone + Copy + std::ops::Add<Output = T> + std::ops::Sub<Output = T>> DiffArray<T> {
        pub fn new(n: usize, v: T) -> Self {
            return DiffArray {
                n: n,
                ds: vec![v; n],
            };
        }

        pub fn add(&mut self, b: usize, e: usize, v: T) {
            if b > e {
                return;
            }
            self.ds[b] = self.ds[b] + v;
            if e + 1 < self.n {
                self.ds[e + 1] = self.ds[e + 1] - v;
            }
        }

        pub fn sum(&mut self) -> Vec<T> {
            let mut res = self.ds.clone();

            for i in 1..self.n {
                res[i] = res[i] + res[i - 1];
            }
            return res;
        }
    }

    // RabinHash(rolling hash) /////////

    pub struct RabinHash {
        H: i64, //
        M: i64, //mod
        hashs: Vec<i64>,
    }

    impl RabinHash {
        pub fn new(s: &String) -> Self {
            let H = 101;
            let M = 1000000000 + 7;
            let mut hashs = vec![0; s.len()];
            hashs[0] = s.as_bytes()[0] as i64 % M;
            for i in 1..s.len() {
                let a = s.as_bytes()[i] as i64;
                hashs[i] = ((hashs[i - 1] * H) % M + a) % M;
            }
            return RabinHash {
                H: H,
                M: M,
                hashs: hashs,
            };
        }

        // get hash value of substring s[b,e]
        pub fn hval(&mut self, b: usize, e: usize) -> i64 {
            let mut v = self.hashs[e];
            if b > 0 {
                let v2 = (self.hashs[b - 1] * mpow(self.H, (e - b + 1) as i64, self.M)) % self.M;
                v -= v2;
                v = (v % self.M + self.M) % self.M;
            }
            return v;
        }
    }

    // math /////////////////

    pub fn mpow(a: i64, n: i64, M: i64) -> i64 {
        if n == 0 {
            return 1;
        }

        let mut r = mpow(a, n / 2, M);
        r = (r * r) % M;
        if n & 1 == 1 {
            r *= a;
        }
        return r % M;
    }

    pub fn inv(a: i64, M: i64) -> i64 {
        return mpow(a, M - 2, M);
    }

    pub fn gcd(a: i64, b: i64) -> i64 {
        if b == 0 {
            return a;
        }
        return gcd(b, a % b);
    }

    pub fn extend_gcd(a: i64, b: i64, x: &mut i64, y: &mut i64) -> i64 {
        if (b == 0) {
            *x = 1;
            *y = 0;
            return a;
        } else {
            let r = extend_gcd(b, a % b, y, x);
            *y -= *x * (a / b);
            return r;
        }
    }

    pub fn inv2(a: i64, M: i64) -> i64 {
        let mut x = 0 as i64;
        let mut y = 0 as i64;
        extend_gcd(a, M, &mut x, &mut y);
        x = (x % M + M) % M;
        return x;
    }

    // io: scanner //////////////////
    use std::io::{stdin, stdout, BufWriter, Write};

    #[derive(Default)]
    pub struct Scanner {
        buffer: Vec<String>,
    }
    impl Scanner {
        pub fn new() -> Self {
            return Scanner { buffer: vec![] };
        }
        pub fn next<T: std::str::FromStr>(&mut self) -> T {
            loop {
                if let Some(token) = self.buffer.pop() {
                    return token.parse().ok().expect("Failed parse");
                }
                let mut input = String::new();
                stdin().read_line(&mut input).expect("Failed read");
                self.buffer = input.split_whitespace().rev().map(String::from).collect();
            }
        }
    }
}









struct Solution {}
fn main() {
    let mut input = algo::Scanner::new();
}
