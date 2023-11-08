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
class BinTree : vector<ll> {
public:
    ll c0 = 0;
    explicit BinTree(ll k = 0) // 默认初始化一个能保存k个元素的空树状数组
    {
        assign(k + 1, 0); // 有效下标从0开始
    }
    int lowbit(ll k)
    {
        return k & -k; // 也可写作x&(x^(x–1))
    }
    ll sum(ll k) // [0,..,k] 的和，k为下标，不是个数
    {
        ll res = _sum(k) + c0;
        return res;
    }
    ll query(ll b, ll e)
    {
        ll res = sum(e);
        if (b > 0) {
            res -= sum(b - 1);
        }
        return res;
    }

    ll _sum(ll k) // 求第1个元素到第n个元素的和
    {
        ll res = (k > 0 ? _sum(k - lowbit(k)) + (*this)[k] : 0);
        return res;
    }
    ll last() // 返回最后一个元素下标
    {
        return size() - 1;
    }
    void add(ll k, ll w) // k 为下标
    {
        if (k == 0) {
            c0 += w;
            return;
        }
        _add(k, w);
    }
    void _add(ll k, ll w) // 为节点k加上w, k为下标
    {
        if (k > last())
            return;
        (*this)[k] += w;
        _add(k + lowbit(k), w);
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
ll inv2(ll a, ll mod)
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

// RabinHash (rolling Hash) //////////////////

struct RabinHash {
    using ll = long long;
    ll h = 101, mod = 1e9 + 7;
    ll n = 0;
    vector<ll> hashs;
    RabinHash(const string& s)
    {
        n = s.size();
        hashs = vector<ll>(n, 0);
        hashs[0] = s[0] % mod;
        for (int i = 1; i < n; i++) {
            ll a = s[i];
            hashs[i] = ((hashs[i - 1] * h) % mod + a) % mod;
        }
    }

    ll mpow(ll a, ll n)
    {
        if (n == 0) {
            return 1;
        }

        ll r = mpow(a, n / 2);
        r = (r * r) % mod;
        if (n & 1) {
            r *= a;
            r %= mod;
        }
        return r;
    }

    // get hash value of substring s[b,e]
    ll hval(ll b, ll e)
    {
        ll v = hashs[e];
        if (b > 0) {
            ll v2 = (hashs[b - 1] * mpow(h, e - b + 1)) % mod;
            v -= v2;
            v = (v % mod + mod) % mod;
        }
        return v;
    }
};

/////////////////////////

template <typename T = ll>
T maxs(const vector<T>& vals, T = 0LL)
{
    return *max_element(vals.begin(), vals.end());
}

template <typename T>
typename std::remove_reference<decltype(*T())>::type maxs(T it_b, T it_e)
{
    return *max_element(it_b, it_e);
}

template <typename T = ll>
T mins(const vector<T>& vals, T = 0LL)
{
    return *min_element(vals.begin(), vals.end());
}

template <typename T>
typename std::remove_reference<decltype(*T())>::type mins(T it_b, T it_e)
{
    return *min_element(it_b, it_e);
}

template <typename T = ll>
T sums(const vector<T>& vals, T = 0LL)
{
    T s = 0;
    for (const T& val : vals) {
        s += val;
    }
    return s;
}

template <typename T>
typename std::remove_reference<decltype(*T())>::type sums(T it_b, T it_e)
{
    typename std::remove_reference<decltype(*T())>::type s = 0;
    T it = it_b;
    while (it != it_e) {
        s += *it;
        it++;
    }
    return s;
}

////////////////////////////

};







int main()
{
    ios_base::sync_with_stdio(false);
    cin.tie(NULL);



    return 0;
}
