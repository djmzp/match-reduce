staload "./string.sats"

dataviewtype Ske =
	| ske_symbol of String	// w+
	| ske_hole of String	// :w+
	| ske_reduce of String	// %w+

viewtypedef skeleton(n: int) = list_vt(Ske, n)
viewtypedef Skeleton = [n: nat] skeleton(n)

fn ske_from_string(String): Ske
fn ske_print(!Ske): void
fn ske_copy(!Ske): Ske
fn ske_free(&Ske >> Ske?):<!wrt> void

fn skeleton_print(!Skeleton): void
fn skeleton_copy(!Skeleton): Skeleton
fn skeleton_free(Skeleton): void

overload gprint with ske_print
overload gfree with ske_free

overload gprint with skeleton_print
overload gfree with skeleton_free
