staload "./string.sats"

dataviewtype Pat =
	| pat_symbol of String	// w+
	| pat_atom of String	// ?w+
	| pat_mult of String	// *w+
	| pat_bal of String		// =w+
	| pat_under				// _
	| pat_ellip				// ...

viewtypedef pattern(n: int) = list_vt(Pat, n)
viewtypedef Pattern = [n: nat] pattern(n)

fn pat_from_string(String): Pat
fn pat_print(!Pat): void
fn pat_copy(!Pat): Pat
fn pat_free(&Pat >> Pat?):<!wrt> void
fn pat_free'(Pat): void

// This is not the actual length but a relative length to discard phrases that may not match
fn pattern_length(!Pattern): [n: nat] int(n)
fn pattern_print(!Pattern): void
fn pattern_copy {n: nat} (!pattern(n)): pattern(n)
fn pattern_free(Pattern): void

overload gprint with pat_print
overload gcopy with pat_copy

overload gprint with pattern_print
overload gfree with pattern_free
