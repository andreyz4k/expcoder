
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

Primitive("map", arrow(arrow(t0, t1), tlist(t0), tlist(t1)), (f -> (xs -> map(f, xs))))
Primitive(
    "unfold",
    arrow(t0, arrow(t0, tbool), arrow(t0, t1), arrow(t0, t0), tlist(t1)),
    (x -> (p -> (h -> (n -> _unfold(x, p, h, n))))),
)
Primitive("range", arrow(tint, tlist(tint)), (n -> collect(0:n-1)))
Primitive("index", arrow(tint, tlist(t0), t0), (j -> (l -> l[j])))
Primitive("tuple2_first", arrow(ttuple2(t0, t1), t0), (t -> t[1]))
Primitive("tuple2_second", arrow(ttuple2(t0, t1), t1), (t -> t[2]))
Primitive(
    "fold",
    arrow(tlist(t0), t1, arrow(t0, t1, t1), t1),
    (itr -> (init -> (op -> foldr((v, acc) -> op(v)(acc), itr, init = init)))),
)
Primitive("length", arrow(tlist(t0), tint), length)

# built-ins
Primitive("if", arrow(tbool, t0, t0, t0), (c -> (t -> (f -> c ? t : f))))
Primitive("+", arrow(tint, tint, tint), (a -> (b -> a + b)))
Primitive("-", arrow(tint, tint, tint), (a -> (b -> a - b)))
Primitive("empty", tlist(t0), [])
Primitive("cons", arrow(t0, tlist(t0), tlist(t0)), (x -> (y -> vcat([x], y))))
Primitive("car", arrow(tlist(t0), t0), first)
Primitive("cdr", arrow(tlist(t0), tlist(t0)), (l -> l[2:end]))
Primitive("empty?", arrow(tlist(t0), tbool), isempty)

[Primitive(string(j), tint, j) for j = 0:1]

Primitive("*", arrow(tint, tint, tint), (a -> (b -> a * b)))
Primitive("mod", arrow(tint, tint, tint), (a -> (b -> a % b)))
Primitive("gt?", arrow(tint, tint, tbool), (a -> (b -> a > b)))
Primitive("eq?", arrow(t0, t0, tbool), (a -> (b -> a == b)))
Primitive("is-prime", arrow(tint, tbool), _is_prime)
Primitive("is-square", arrow(tint, tbool), (n -> floor(sqrt(n))^2 == n))

Primitive("repeat", arrow(t0, tint, tlist(t0)), (x -> (n -> fill(x, n))))
Primitive("zip2", arrow(tlist(t0), tlist(t1), tlist(ttuple2(t0, t1))), (a -> (b -> zip(a, b))))
