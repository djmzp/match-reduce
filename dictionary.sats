staload "expression.sats"

viewtypedef dictionary(n: int) = list_vt(@(Strptr1, Expression), n)
viewtypedef Dictionary = [n: nat] dictionary(n)

fn dictionary_new(): dictionary(0)
fn dictionary_print(!Dictionary): void
fn dictionary_free(Dictionary): void

overload gprint with dictionary_print
