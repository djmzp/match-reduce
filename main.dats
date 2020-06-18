
#include "share/atspre_staload.hats"
// #define ATS_DYNLOADFLAG 0

staload "dictionary.sats"
staload "expression.sats"		// XXX probably change the name in the future // maybe "phrase"?
staload "pattern.sats"
staload "skeleton.sats"

overload close with fileref_close

/*
	100 r_sum: ?x + ?y => $sum :x :y ;
*/

viewtypedef Rule = @{
	level = int,
	precedence = int,
	name = string,
	pattern = Pattern,
	skeleton = Skeleton
}

dataviewtype Exp =
	| num of int
	| str of Strnptr
	| pat of Pattern
	| ske of Skeleton


fun free_exp(e: List_vt(Exp)): void =
	case+ e of
	| ~list_vt_cons(~num(_), es) => free_exp(es)
	| ~list_vt_cons(~str(s), es) => (strnptr_free(s); free_exp(es))
	| ~list_vt_cons(~pat(p), es) => (pattern_free(p); free_exp(es))
	| ~list_vt_cons(~ske(s), es) => (skeleton_free(s); free_exp(es))
	| ~list_vt_nil() => ()


#define :: list_vt_cons

fun lookup(symbol: !Strptr1, dict: !Dictionary): Option_vt(Expression) =
	case+ dict of
	| list_vt_cons(x, ds) when compare_strptr_strptr(x.0, symbol) = 0 =>
		Some_vt(expression_copy(x.1))
	| list_vt_cons(_, ds) => lookup(symbol, ds)
	| list_vt_nil() => None_vt()

fn match(pat: !Pattern, exp: !Expression): Option_vt(Dictionary) =
	let
		val dict = dictionary_new();

		fun loop {n: nat} (pat: !Pattern, exp: !Expression, dict: dictionary(n), temp: Expression): Option_vt(Dictionary) =
			case+ (pat, exp) of
			| (pat_symbol(s1)::ps, s2::es) when compare(s2, s1) = 0 => loop(ps, es, dict, temp) where {
				// XXX ????? why am I extending the dictionary here anyways
				// val dict' = list_vt_extend(dict, (s1, s2 :: list_vt_nil))
			}
			| (pat_symbol(s1)::ps, s2::es) => (
				dictionary_free(dict);
				expression_free(temp);
				None_vt()
			)
			| (pat_atom(s1)::ps, s2::es) => loop(ps, es, dict', temp) where {
				// val dict' = list_vt_extend(dict, (strptr1_copy(s1), strptr1_copy(s2) :: list_vt_nil))
				val dict' = list_vt_cons((strptr1_copy(s1), strptr1_copy(s2) :: list_vt_nil), dict)
			}
			// PATTERN: some thing *what ever => ...  |||| and the expression is empty, dont match
			| (pat_mult(s1)::_, list_vt_nil()) => (
				expression_free(temp);
				Some_vt(dict)
			)
			// PATTERN: some thing *end => ...
			| (pat_mult(s1)::list_vt_nil(), _) => Some_vt(dict') where {
				val () = expression_free(temp)
				// val dict' = list_vt_extend(dict, (strptr1_copy(s1), expression_copy(exp)))
				val dict' = list_vt_cons((strptr1_copy(s1), expression_copy(exp)), dict)
			}
			// PATTERN: some thing *alot end => ...
			| (pat_mult(s1)::pat_symbol(lookahead)::ps, s2::es) when compare(s2, lookahead) = 0 =>
			let
				val temp' = expression_copy(temp)
				val () = expression_free(temp)
				val temp = $list_vt{Strptr1}()
				// val dict' = list_vt_extend(dict, (strptr1_copy(s1), temp'))
				val dict' = list_vt_cons((strptr1_copy(s1), temp'), dict)
			in
				loop(ps, es, dict', temp)
			end

			| (pat_mult(s1)::pat_symbol(lookahead)::ps, s2::es) =>
			let
				// XXX this used to be extend
				// val tmp = list_vt_append(temp, s2::list_vt_nil())
				// val tmp = list_vt_extend(temp, strptr1_copy(s2))
				val tmp = list_vt_cons(strptr1_copy(s2), temp)
			in
				loop(pat, es, dict, tmp)
			end
			// XXX maybe not?
			| (list_vt_nil(), _) => (
				expression_free(temp);
				Some_vt(dict)
			)

			| (_, _) => (
				// Lets try to be positive
				// dictionary_free(dict);
				expression_free(temp);
				Some_vt(dict)
			)

	in
		loop(pat, exp, dict, $list_vt{Strptr1}())
	end

fn instantiate(ske: !Skeleton, dict: !Dictionary): Option_vt(Expression) =
	let
		val exp: Expression = expression_new()
		fun loop(ske: !Skeleton, dict: !Dictionary, exp: Expression): Option_vt(Expression) =
			case+ ske of
			| ske_symbol(s)::ss => loop(ss, dict, exp') where {
				// XXX this used to be extend
				val exp' = list_vt_append(strptr1_copy(s)::list_vt_nil, exp)
			}
			| ske_hole(s)::ss => (
				case+ lookup(s, dict) of
				// TODO way too many (two, to be exact) reverses
				| ~Some_vt(def) => loop(ss, dict, list_vt_append(list_vt_reverse(def), exp))
				| ~None_vt() => (
					expression_free(exp);
					None_vt()
				)
			)
			// TODO See if its possible to reverse exp as we're iterating
			// the skeleton data structure for performance, instead of
			// reversing it here
			| list_vt_nil() => Some_vt(list_vt_reverse(exp))
	in
		loop(ske, dict, exp)
	end

fun read_file(name: string): void =
	let
		val name = "main.dats"
		val file_ref = fileref_open_opt(name, file_mode_r)
	in
		case+ file_ref of
		| ~None_vt() => println!("File ", name, " does not exist")
		| ~Some_vt(file) =>
			let
				implement fileref_get_word$isalpha<>(c) =
					not (c = ' ' || c = '\t' || c = '\n' || c = '\v' || c = '\f' || c = '\r')

				val word = fileref_get_word(file)
				val () = println!(word)
				val () = free(word)
				val word = fileref_get_word(file)
			in
				println!(word);
				free(word);
				close(file)
			end
	end

// #include "tests.dats"

viewtypedef strnptr11(n: int) = [l: agz] strnptr(l, n)

viewtypedef Strnptr11 = [n: nat | n > 0] strnptr11(n)



fn head {n: int | n > 0} (s: !strnptr11(n)): char = s[0]
/*
fn parse {n: nat} (s: !strnptr1(n)): List_vt(strptr) =
	let
		val len = length(s)
		fun loop (s: !strnptr1(n), i: size_t): void =
			ifcase
			| i < len => ()
			| _ => ()
	in
		loop(s, i2sz(0));
		list_vt_nil()
	end
*/

/*
	parse_rule =
	case+ x of
	| precedence :: name :: pattern :: skeleton => make_rule(precedence, name, etc)
	| _ => error
*/

// fn parse_rule()


fn alt_or(x: Option_vt(int), y: Option_vt(int)): Option_vt(int) =
	case+ (x, y) of
	| (Some_vt(_), _) => (option_vt_free(y); x)
	| (None_vt(), Some_vt(_)) => (option_vt_free(x); y)
	| (_ , _) => (option_vt_free(x); option_vt_free(y); None_vt())

infixl 50 <|>
overload <|> with alt_or

extern castfn sz2i {n: int} (x: ssize_t(n)): int(n)

fn option_vt_print(x: !Option_vt(int)): void =
	case+ x of
	| Some_vt(f) => (print("Some "); print(f))
	| None_vt() => print("None")

extern fun atoi(s: !Strnptr): int = "mac#"


fn {a: viewt@ype} stream_vt_uncons(st: stream_vt(a)): Option_vt(@(a, stream_vt(a))) =
	let
		val s = !st
	in
		case+ s of
		| ~stream_vt_cons(x, xs) => Some_vt(@(x, xs))
		| ~stream_vt_nil() => None_vt()
	end

fn strnptr2int {m: nat | m > 0} (s: strnptr(m)): Option_vt(int) =
	let
		val len: int(m) = sz2i(length(s))
		fun loop {n: nat | n < m} (s: !strnptr(m), i: int(n)): bool =
			if isdigit(strnptr_get_at_size(s, i2sz(i))) then
				if i + 1 < len then
					loop(s, i + 1)
				else
					true
			else
				false
	in
		if loop(s, 0) then
			let
				val n = atoi(s)
			in
				strnptr_free(s);
				Some_vt(n)
			end
		else (
			strnptr_free(s);
			None_vt()
		)
	end

fn parse_string(st: stream_vt(Strnptr)): Option_vt(@(Exp, stream_vt(Strnptr))) =
	let
		val st' = stream_vt_uncons<Strnptr>(st)
	in
		case+ st' of
		| ~Some_vt(t) => Some_vt(@(str(t.0), t.1))
		| ~None_vt() => None_vt()
	end

fn parse_int(st: stream_vt(Strnptr)): Option_vt(@(Exp, stream_vt(Strnptr))) =
	let
		val st' = stream_vt_uncons<Strnptr>(st)
	in
		case+ st' of
		| ~Some_vt(t) when length(t.0) > 0 =>
			let
				val t_st: stream_vt(Strnptr) = t.1
				val t_s: Strnptr = t.0
				val n_opt = strnptr2int(t_s)
			in
				case+ n_opt of
				| ~Some_vt(n) => Some_vt(@(num(n), t_st))
				| ~None_vt() => (
					stream_vt_free(t_st);
					None_vt()
				)
			end
		| ~Some_vt(t) => (
			strnptr_free(t.0);
			stream_vt_free(t.1);
			None_vt()
		)
		| ~None_vt() => None_vt()
	end


fn pat_from_strnptr {n: int | n > 0} (s: strnptr11(n)): Pat =
	case+ head(s) of
	| '?' => pat_atom(strnptr2strptr(s))
	| '*' => pat_mult(strnptr2strptr(s))
	| _ => pat_symbol(strnptr2strptr(s))

fn parse_pat(st: stream_vt(Strnptr11)): Option_vt(@(Exp, stream_vt(Strnptr))) =
	let
		fun loop {n: nat} (st: stream_vt(Strnptr11), p: pattern(n)): Option_vt(@(Exp, stream_vt(Strnptr11))) =
			let
				val st = stream_vt_uncons<Strnptr11>(st)
			in
				case+ st of
				| ~None_vt() => (
					pattern_free(p);
					None_vt()
				)
				| ~Some_vt(t) =>
					let
						val st = t.1
						val s = t.0
						val d = strnptr_copy(s)
						val d = strnptr2string(d)
						val eq = eq_string_string(d , "=>")
					in
						if eq then (
							strnptr_free(s);
							Some_vt(@(pat(p), st))
						) else (
							loop(st, list_vt_cons(pat_from_strnptr(s), p))
						)
					end
			end
	in
		loop(st, $list_vt{Pat}())
	end

/*
fn parse_pattern(st: stream_vt(Strnptr)): @(stream_vt(Strnptr), Option_vt(Exp)) =
	let
		val st' = stream_vt_uncons(st)
	in
		case+ st' of
		| ~Some_vt(t) =>
	end
*/

fun streamize_fileref_word(file: FILEref): stream_vt(Strnptr11) =
	$ldelay(
		if fileref_is_eof(file) then
			stream_vt_nil()
		else
			let
				implement fileref_get_word$isalpha<>(c) =
					not (c = ' ' || c = '\t' || c = '\n' || c = '\v' || c = '\f' || c = '\r')
				val st = strptr2strnptr(fileref_get_word(file))
			in
				if strnptr_isnot_null(st) * (strnptr_length(st) > 0) then
					stream_vt_cons(
						st,
						streamize_fileref_word(file)
					)
				else (
					strnptr_free(st);
					stream_vt_nil())
			end
	)

fn print_ex(e: !Exp): void =
	case+ e of
	| num(n) => print(n)
	| str(s) => print(s)
	| pat(p) => pattern_print(p)
	| ske(s) => skeleton_print(s)

fn free_ex(e: Exp): void =
	case+ e of
	| ~num(n) => ()
	| ~str(s) => strnptr_free(s)
	| ~pat(p) => pattern_free(p)
	| ~ske(s) => skeleton_free(s)

typedef Parser(a: viewt@ype) = stream_vt(Strnptr) -<fun1> Option_vt(@(a, stream_vt(Strnptr)))
viewtypedef Parser_vt(a: viewt@ype) = stream_vt(Strnptr) -<cloptr> Option_vt(@(a, stream_vt(Strnptr)))

// fn pipe(p1: !Parser(Exp), p2: !Parser(Exp)): () -<cloref1> int = lam(): int => let in 0 end
/*
fun
make_rand
(
// argumentless
) : () -<cloref1> ulint = let
  val state = ref<ulint> (22222UL)
in
//
lam() : ulint => let
  val old = !state
  val new = (old * 196314165UL) + 907633515UL
  val ((*void*)) = !state := new
in
  new
end // end of [lam]
//
end // end of [make_rand]
*/


fn parse_rule(st: stream_vt(Strnptr)): void = // Option_vt(@(Exp, stream_vt(Strnptr))) =
	let
		val level = parse_int(st)
	in
		case+ level of
		| ~None_vt() => println!("got nothn") // None_vt()
		| ~Some_vt(t) =>
			let
				val l = t.0
				val- num(x) = l
				val prec = parse_int(t.1)
				val () = println!("Got level: ", x)
			in
				case+ prec of
				| ~None_vt() => free_ex(l)
				| ~Some_vt(t) =>
					let
						val p = t.0
						val name = parse_string(t.1)
					in
						case+ name of
						| ~None_vt() => (free_ex(l); free_ex(p))
						| ~Some_vt(t) =>
							let
								val n = t.0
							in
								println!();
								print_ex(l);
								print(" ");
								print_ex(p);
								print(" ");
								print_ex(n);
								println!();
								free_ex(l);
								free_ex(p);
								free_ex(n);
								stream_vt_free(t.1)
							end
					end

			end
	end

implement main0() =
	let
		val stream = streamize_fileref_word(stdin_ref)
	in
		parse_rule(stream)
		// free(stream)
	end

////
implement main0() =
	let
		implement fileref_get_word$isalpha<>(c) =
			not (c = ' ' || c = '\t' || c = '\n' || c = '\v' || c = '\f' || c = '\r')
		val x = strptr2strnptr(fileref_get_word(stdin_ref))
		val () = assertloc(length(x) > 0)
		val d = parse_int(x)
	in
		(case- d of
		| ~Some_vt(~num(n)) => println!(n)
		| ~None_vt() => ());
		free(x)
	end


////
implement main0() =
	let
		val exps = expression_new()
		fun loop(): void =
			let
				val x: Strnptr = strptr2strnptr(fileref_get_word(stdin_ref))

			in
				println!(x);
				if strnptr_isnot_null x then
					if eq_strptr_string(x, "q") then (
						free(x);
					) else (
						free(x);
						loop()
					)
				else
					free(x);
			end
	in
		loop();
		expression_free(exps)
	end
