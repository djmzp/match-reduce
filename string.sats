viewtypedef strnptr11(n: int) = [l: agz] strnptr(l, n)
viewtypedef Strnptr11 = [n: nat | n > 0] strnptr11(n)
viewtypedef String = Strnptr11

fn string_new {n: nat | n > 0} (string(n)): String
fn string_copy(!String): String
fn string_compare(!String, !String): Sgn
fn string_print(!String): void
fn string_cut_head {n: int | n > 0} (s: !strnptr11(n)): void
fn string_free(String):<!wrt> void

overload gcopy with string_copy
overload compare with string_compare
overload gprint with string_print
overload gfree with string_free
