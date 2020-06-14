dataviewtype Pat =
	| pat_symbol of Strptr1	// w+
	| pat_atom of Strptr1	// ?w+
	| pat_mult of Strptr1	// *w+

viewtypedef pattern(n: int) = list_vt(Pat, n)
viewtypedef Pattern = [n: nat] pattern(n)

fn pat_print(!Pat): void
fn pat_free(&Pat >> Pat?):<!wrt> void

fn pattern_print(!Pattern): void
fn pattern_free(Pattern): void

overload gprint with pat_print

overload gprint with pattern_print
