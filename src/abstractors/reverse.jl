@define_reverse_primitive("reverse", arrow(tlist(t0), tlist(t0)), (a -> reverse(a)), ((_, a) -> [reverse(a)]))
