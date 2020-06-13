#include "share/atspre_staload.hats"


#include "main.dats"

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

implement fprint_list_vt$sep<>(out) = print(" ");

// TODO once I find the way of implementing my own print() functions for 
// my custom datatypes without gcc dying, clear everything up
macdef test(num, pat, ske, exp, expect) = 
	let
		val pat = ,(pat)
		val ske = ,(ske)
		val exp = ,(exp)
		val () = println!("TEST ", ,(num));
		val- ~Some_vt(dict) = match(pat, exp)
		val- ~Some_vt(exp_out) = instantiate(ske, dict)
		val expct = ,(expect)
		// implement list_vt_equal$eqfn<string>(s1, s2) = strcmp(s1, s2) = 0
		val passed = list_vt_equal_string(exp_out, expct)
			
	in
		print("RULE: ");
		pattern_list_print(pat);
		print("=> ");
		skeleton_list_print(ske);
		println!();
		println!();
		dictionary_print(dict);
		println!("IN: ", exp);
		println!("OUT: ", exp_out);

		(if passed then
			println!("PASSED")
		else
			println!("FAILED"));
		
		println!();
		println!("--------------------------------------------------");
		
		dictionary_free(dict);
		expression_free(exp);
		list_vt_free(expct);
		pattern_free(pat);
		expression_free(exp_out);	
		skeleton_free(ske)
	end

// Test-based semantics: the only way to go

fn test1(): void = test(
	1,
	$list_vt{Pat}(pat_atom("a"), pat_atom("b"), pat_atom("c")),
	$list_vt{Ske}(ske_hole("c"), ske_hole("b"), ske_hole("a")),
	$list_vt{string}("foo", "bar", "baz"),
	$list_vt{string}("baz", "bar", "foo")
)
	
fn test2(): void = test(
	2,
	$list_vt{Pat}(pat_mult("a")),
	$list_vt{Ske}(ske_symbol("B"), ske_hole("a"), ske_symbol("C")),
	$list_vt{string}("foo", "bar", "baz"),
	$list_vt{string}("B", "foo", "bar", "baz", "C")
)

fn test3(): void = test(
	3,
	$list_vt{Pat}(pat_mult("a"), pat_symbol("C")),
	$list_vt{Ske}(ske_hole("a")),
	$list_vt{string}("foo", "bar", "C"),
	$list_vt{string}("foo", "bar")
)

fn test4(): void = test(
	4,
	$list_vt{Pat}(pat_symbol("A"), pat_symbol("C"), pat_mult("a")),
	$list_vt{Ske}(ske_hole("a")),
	$list_vt{string}("A", "C", "foo", "bar"),
	$list_vt{string}("foo", "bar")
)

fn test5(): void = test(
	5,
	$list_vt{Pat}(pat_symbol("A"), pat_symbol("B")),
	$list_vt{Ske}(),
	$list_vt{string}("A", "B", "C"),
	$list_vt{string}()
)

fn test6(): void = test(
	6,
	$list_vt{Pat}(pat_mult("a"), pat_symbol("B"), pat_symbol("C")),
	$list_vt{Ske}(ske_hole("a")),
	$list_vt{string}("B", "C"),
	$list_vt{string}()
)

fn test7(): void = test(
	7,
	$list_vt{Pat}(pat_mult("a"), pat_symbol("B"), pat_mult("c")),
	$list_vt{Ske}(ske_hole("a"), ske_hole("c")),
	$list_vt{string}("A", "F", "E", "B", "C"),
	$list_vt{string}("A", "F", "E", "C")
)

fn test8(): void = test(
	8,
	$list_vt{Pat}(pat_mult("a"), pat_symbol("B"), pat_mult("c"), pat_symbol("D")),
	$list_vt{Ske}(ske_hole("a"), ske_hole("c")),
	$list_vt{string}("B", "D"),
	$list_vt{string}()
)

fn test9(): void = test(
	9,
	$list_vt{Pat}(pat_atom("a"), pat_symbol("B")),
	$list_vt{Ske}(ske_hole("a")),
	$list_vt{string}("B"),
	$list_vt{string}()
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

implement main0() = run_tests()

