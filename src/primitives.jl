
function _unfold(x, p, h, n)
    acc = []
    while !p(x)
        push!(acc, h(x))
        x = n(x)
    end
    acc
end

_is_prime(n) = in(
    n,
    Set([
        2,
        3,
        5,
        7,
        11,
        13,
        17,
        19,
        23,
        29,
        31,
        37,
        41,
        43,
        47,
        53,
        59,
        61,
        67,
        71,
        73,
        79,
        83,
        89,
        97,
        101,
        103,
        107,
        109,
        113,
        127,
        131,
        137,
        139,
        149,
        151,
        157,
        163,
        167,
        173,
        179,
        181,
        191,
        193,
        197,
        199,
    ]),
)

Primitive("map", arrow(arrow(t0, t1), tlist(t0), tlist(t1)), map)
Primitive("unfold", arrow(t0, arrow(t0, tbool), arrow(t0, t1), arrow(t0, t0), tlist(t1)), _unfold)
Primitive("range", arrow(tint, tlist(tint)), (n -> range(0, n)))
Primitive("index", arrow(tint, tlist(t0), t0), ((j, l) -> l[j]))
Primitive("fold", arrow(tlist(t0), t1, arrow(t0, t1, t1), t1), ((itr, init, op) -> foldl(op, itr, init = init)))
Primitive("length", arrow(tlist(t0), tint), length)

# built-ins
Primitive("if", arrow(tbool, t0, t0, t0), ((c, t, f) -> c ? t : f))
Primitive("+", arrow(tint, tint, tint), +)
Primitive("-", arrow(tint, tint, tint), -)
Primitive("empty", tlist(t0), [])
Primitive("cons", arrow(t0, tlist(t0), tlist(t0)), ((x, y) -> vcat([x], y)))
Primitive("car", arrow(tlist(t0), t0), first)
Primitive("cdr", arrow(tlist(t0), tlist(t0)), (l -> l[2:end]))
Primitive("empty?", arrow(tlist(t0), tbool), isempty)

[Primitive(string(j), tint, j) for j in 0:1]

Primitive("*", arrow(tint, tint, tint), *)
Primitive("mod", arrow(tint, tint, tint), %)
Primitive("gt?", arrow(tint, tint, tbool), >)
Primitive("eq?", arrow(tint, tint, tbool), ==)
Primitive("is-prime", arrow(tint, tbool), _is_prime)
Primitive("is-square", arrow(tint, tbool), (n -> floor(sqrt(n))^2 == n))
