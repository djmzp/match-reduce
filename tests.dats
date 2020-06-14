#include "share/atspre_staload.hats"

/*
// XXX This doesn't work. But why
extern fn {a: t@ype} list_vt_equal$eqfn(x: a, y: a): bool

fun {a: t@ype} list_vt_equal(lx: !List_vt(a), ly: !List_vt(a)): bool =
	case+ (lx, ly) of
	| (list_vt_cons(x, xs), list_vt_cons(y, ys)) =>
		if list_vt_equal$eqfn<a>(x, y) then
			list_vt_equal(xs, ys)
		else
			false
	| (list_vt_nil(), list_vt_nil()) => true
	| (list_vt_cons(_, _), list_vt_nil()) => false
	| (list_vt_nil(), list_vt_cons(_,_)) => false
*/

fun list_vt_equal_string(lx: !List_vt(string), ly: !List_vt(string)): bool =
	case+ (lx, ly) of
	| (list_vt_cons(x, xs), list_vt_cons(y, ys)) =>
		if strcmp(x, y) = 0 then
			list_vt_equal_string(xs, ys)
		else
			false
	| (list_vt_nil(), list_vt_nil()) => true
	| (list_vt_cons(_, _), list_vt_nil()) => false
	| (list_vt_nil(), list_vt_cons(_,_)) => false


fn convert(l: List_vt(string)): [n: nat] expression(n) =
	let
		fun loop {n: nat} (l: List_vt(string), exp: list_vt(Strptr1, n)): Expression =
			case+ l of
			| ~list_vt_cons(x, xs) => loop(xs, list_vt_cons(string0_copy(x), exp))
			| ~list_vt_nil() => exp
	in
		loop(list_vt_reverse(l), $list_vt{Strptr1}())
	end



implement fprint_list_vt$sep<>(out) = print(" ");

macdef test(num, pat, ske, exp, expect) =
	let
		val pat = ,(pat)
		val ske = ,(ske)
		val exp: Expression = convert(,(exp))
		val () = println!("TEST ", ,(num));
		val- ~Some_vt(dict) = match(pat, exp)
		val- ~Some_vt(exp_out) = instantiate(ske, dict)
		val expct = convert(,(expect))
	in
		gprint!("RULE: ", pat, "=> ", ske, "\n\nIN: ", exp, "\nOUT: ", exp_out, "\n", dict);

		(if exp_out = expct then
			println!("PASSED")
		else
			println!("FAILED"));

		println!();
		println!("--------------------------------------------------");

		dictionary_free(dict);
		expression_free(exp);
		expression_free(expct);
		pattern_free(pat);
		expression_free(exp_out);
		skeleton_free(ske)
	end

// Test-based semantics: the only way to go
macdef sc = string0_copy

fn test1(): void = test(
	1,
	$list_vt{Pat}(pat_atom(sc"a"), pat_atom(sc"b"), pat_atom(sc"c")),
	$list_vt{Ske}(ske_hole(sc"c"), ske_hole(sc"b"), ske_hole(sc"a")),
	$list_vt{string}("foo", "bar", "baz"),
	$list_vt{string}("baz", "bar", "foo")
)

fn test2(): void = test(
	2,
	$list_vt{Pat}(pat_mult(sc"a")),
	$list_vt{Ske}(ske_symbol(sc"B"), ske_hole(sc"a"), ske_symbol(sc"C")),
	$list_vt{string}("foo", "bar", "baz"),
	$list_vt{string}("B", "foo", "bar", "baz", "C")
)

fn test3(): void = test(
	3,
	$list_vt{Pat}(pat_mult(sc"a"), pat_symbol(sc"C")),
	$list_vt{Ske}(ske_hole(sc"a")),
	$list_vt{string}("foo", "bar", "C"),
	$list_vt{string}("foo", "bar")
)

fn test4(): void = test(
	4,
	$list_vt{Pat}(pat_symbol(sc"A"), pat_symbol(sc"C"), pat_mult(sc"a")),
	$list_vt{Ske}(ske_hole(sc"a")),
	$list_vt{string}("A", "C", "foo", "bar"),
	$list_vt{string}("foo", "bar")
)

fn test5(): void = test(
	5,
	$list_vt{Pat}(pat_symbol(sc"A"), pat_symbol(sc"B")),
	$list_vt{Ske}(),
	$list_vt{string}("A", "B", "C"),
	$list_vt{string}()
)

fn test6(): void = test(
	6,
	$list_vt{Pat}(pat_mult(sc"a"), pat_symbol(sc"B"), pat_symbol(sc"C")),
	$list_vt{Ske}(ske_hole(sc"a")),
	$list_vt{string}("B", "C"),
	$list_vt{string}()
)

fn test7(): void = test(
	7,
	$list_vt{Pat}(pat_mult(sc"a"), pat_symbol(sc"B"), pat_mult(sc"c")),
	$list_vt{Ske}(ske_hole(sc"a"), ske_hole(sc"c")),
	$list_vt{string}("A", "F", "E", "B", "C"),
	$list_vt{string}("A", "F", "E", "C")
)

fn test8(): void = test(
	8,
	$list_vt{Pat}(pat_mult(sc"a"), pat_symbol(sc"B"), pat_mult(sc"c"), pat_symbol(sc"D")),
	$list_vt{Ske}(ske_hole(sc"a"), ske_hole(sc"c")),
	$list_vt{string}("B", "D"),
	$list_vt{string}()
)

fn test9(): void = test(
	9,
	$list_vt(pat_atom(sc"a"), pat_symbol(sc"B")),
	$list_vt(ske_hole(sc"a")),
	$list_vt("B", "B"),
	$list_vt("B")
)

fn run_tests(): void = (
	test1();
	test2();
	test3();
	test4();
	test5();
	test6();
	test7();
	test8();
	test9()
)



