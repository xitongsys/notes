#include <bits/stdc++.h>
using namespace std;

using ll = long long;
using pll = pair<ll, ll>;
using pii = pair<int, int>;

namespace algos {

// Segment Tree /////////////////////
struct Sum {
    static long long op(long long v1, long long v2)
    {
        return v1 + v2;
    }
};
struct Max {
    static long long op(long long v1, long long v2)
    {
        return max(v1, v2);
    }
};
struct Min {
    static long long op(long long v1, long long v2)
    {
        return min(v1, v2);
    }
};

template <class Op>
struct SegTree {

    struct Node {
        long long lpos, rpos;
        long long val, d;
        Node()
        {
            lpos = rpos = 0;
            val = d = 0;
        }
    };

    vector<Node> nodes;

    SegTree(long long lpos, long long rpos)
    {
        long long n = (rpos - lpos + 1);
        nodes = vector<Node>(n * 4 + 1);
        init(0, lpos, rpos);
    }

    void init(long long u, long long lpos, long long rpos)
    {
        nodes[u].lpos = lpos;
        nodes[u].rpos = rpos;
        if (lpos == rpos)
            return;
        long long mpos = lpos + (rpos - lpos) / 2;
        long long lu = 2 * u + 1, ru = 2 * u + 2;
        if (lu < nodes.size())
            init(lu, lpos, mpos);
        if (ru < nodes.size())
            init(2 * u + 2, mpos + 1, rpos);
    }

    void pushdown(long long u)
    {
        if (nodes[u].d == 0)
            return;
        long long lu = 2 * u + 1, ru = 2 * u + 2;
        if (lu < nodes.size()) {
            nodes[lu].val += nodes[u].d;
            nodes[lu].d += nodes[u].d;
        }
        if (ru < nodes.size()) {
            nodes[ru].val += nodes[u].d;
            nodes[ru].d += nodes[u].d;
        }
        nodes[u].d = 0;
    }

    void add(long long lpos, long long rpos, long long d, long long u = 0)
    {
        if (lpos == nodes[u].lpos && rpos == nodes[u].rpos) {
            nodes[u].d += d;
            nodes[u].val += d;
            return;
        }
        pushdown(u);
        long long mpos = nodes[u].lpos + (nodes[u].rpos - nodes[u].lpos) / 2;
        long long lu = 2 * u + 1, ru = 2 * u + 2;
        if (rpos <= mpos) {
            add(lpos, rpos, d, lu);
        } else if (lpos > mpos) {
            add(lpos, rpos, d, ru);
        } else {
            add(lpos, mpos, d, lu);
            add(mpos + 1, rpos, d, lu);
        }

        nodes[u].val = Op::op(nodes[lu].val, nodes[ru].val);
    }

    void set(long long pos, long long val)
    {
        long long val_old = query(pos, pos);
        add(pos, pos, val - val_old);
    }

    long long query(long long lpos, long long rpos, long long u = 0)
    {
        if (nodes[u].lpos == lpos && nodes[u].rpos == rpos) {
            return nodes[u].val;
        }
        pushdown(u);

        long long mpos = nodes[u].lpos + (nodes[u].rpos - nodes[u].lpos) / 2;
        long long lu = 2 * u + 1, ru = 2 * u + 2;
        if (rpos <= mpos) {
            return query(lpos, rpos, lu);
        } else if (lpos > mpos) {
            return query(lpos, rpos, ru);
        } else {
            return Op::op(query(lpos, mpos, lu), query(mpos + 1, rpos, ru));
        }
    }
};
/////////////////////

// Index Tree
class BinTree : vector<long long> {
public:
    explicit BinTree(long long k = 0) // ??????????k?????????
    {
        assign(k + 1, 0); // ?????1??,0??????
    }
    long long lowbit(long long k)
    {
        return k & -k;
        // ????x&(x^(x1))
    }
    long long sum(long long k) // ??1?????n?????
    {
        return k > 0 ? sum(k - lowbit(k)) + (*this)[k] : 0;
    }
    long long last() // ??????????
    {
        return size() - 1;
    }
    void add(long long k, long long w) // ???k??w
    {
        if (k > last())
            return;
        (*this)[k] += w;
        add(k + lowbit(k), w);
    }
};

/////////////////////

// GCD /////////////

ll mpow(ll a, ll n, ll mod)
{
    if (n == 0)
        return 1;
    ll r = mpow(a, n / 2, mod);
    r *= r;
    r %= mod;
    if (n % 2)
        r *= a;
    return r % mod;
}

ll inv(ll a, ll mod)
{
    return mpow(a, mod - 2, mod);
}

ll gcd(ll a, ll b)
{
    if (b == 0)
        return a;
    return gcd(b, a % b);
}

ll extend_gcd(ll a, ll b, ll& x, ll& y)
{
    if (b == 0) {
        x = 1, y = 0;
        return a;
    } else {
        ll r = extend_gcd(b, a % b, y, x);
        y -= x * (a / b);
        return r;
    }
}
ll inv(ll a, ll mod)
{
    ll x, y;
    extend_gcd(a, mod, x, y);
    x = (x % mod + mod) % mod;
    return x;
}

//////////////////////////

// DiffArray /////////////

template <class T>
class DiffArray {
public:
    int n;
    vector<T> ds;
    DiffArray(int n, int v = 0)
    {
        this->n = n;
        ds = vector<T>(n, v);
    }

    void add(int b, int e, T v)
    {
        if (b > e) {
            return;
        }
        ds[b] += v;
        if (e + 1 < n) {
            ds[e + 1] -= v;
        }
    }

    vector<T> sum()
    {
        vector<T> res = ds;
        for (int i = 1; i < n; i++) {
            res[i] += res[i - 1];
        }
        return res;
    }
};

////////////////////////////

};

int main()
{
    return 0;
}