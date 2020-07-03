staload "./string.sats"

dataviewtype Pat =
	| pat_symbol of String	// w+
	| pat_atom of String	// ?w+
	| pat_mult of String	// *w+
	// TODO add placeholders _ and ...

viewtypedef pattern(n: int) = list_vt(Pat, n)
viewtypedef Pattern = [n: nat] pattern(n)

fn pat_from_string(String): Pat
fn pat_print(!Pat): void
fn pat_copy(!Pat): Pat
fn pat_free(&Pat >> Pat?):<!wrt> void

fn pattern_print(!Pattern): void
fn pattern_copy(!Pattern): Pattern
fn pattern_free(Pattern): void

overload gprint with pat_print

overload gprint with pattern_print
