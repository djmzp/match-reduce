dataviewtype Ske =
	| ske_symbol of Strptr1	// w+
	| ske_hole of Strptr1	// :w+

viewtypedef skeleton(n: int) = list_vt(Ske, n)
viewtypedef Skeleton = [n: nat] skeleton(n)

fn ske_print(!Ske): void
fn ske_free(&Ske >> Ske?):<!wrt> void

fn skeleton_print(!Skeleton): void
fn skeleton_free(Skeleton): void

overload gprint with ske_print

overload gprint with skeleton_print
