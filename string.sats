viewtypedef strnptr11(n: int) = [l: agz] strnptr(l, n)
viewtypedef Strnptr11 = [n: nat | n > 0] strnptr11(n)
viewtypedef String = Strnptr11

fn string_new {n: nat | n > 0} (string(n)): String
fn string_copy(!String): String
fn string_compare(!String, !String): int
fn string_equal(!String, !String): bool
// For comparison with stack allocated strings
fn string_compare_stack {n: nat | n > 0} (!String, string(n)): int
fn string_equal_stack {n: nat | n > 0} (!String, string(n)): bool
fn string_print(!String): void
fn string_cut_head {n: int | n > 0} (s: !strnptr11(n)): void
fn string_free(String):<!wrt> void

overload gcopy with string_copy
overload compare with string_compare
overload = with string_equal
overload compare with string_compare_stack
overload = with string_equal_stack
overload gprint with string_print
overload gfree with string_free
