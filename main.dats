#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0

//#include "share/HATS/atspre_staload_libats_ML.hats"

/*
	100 r_sum: ?x + ?y => $sum :x :y ;
*/

overload close with fileref_close

typedef Parser(a: t@ype) = string -> List_vt(a)

dataviewtype Pat = 
	| pat_symbol of string	// w+
	| pat_atom of string	// ?w+
	| pat_mult of string	// *w+

dataviewtype Ske =
	| ske_symbol of string	// w+
	| ske_hole of string	// :w+

viewtypedef Expression = List_vt(string)
viewtypedef Pattern = List_vt(Pat)
viewtypedef Skeleton = List_vt(Ske)

viewtypedef Rule = @{
	precedence = int,
	name = string,
	pattern = Pattern,
	skeleton = Skeleton
}

// TODO Pattern and Pat are used interchangeably but they are not the same
// change the name of the functions / whatever necessary to keep them
// consistent,
// for example: pattern_free to pattern_list_free or something
// or rather: pattern_print to pat_print

fun pattern_free(pat: Pattern): void =
	let
		implement list_vt_freelin$clear<Pat>(e) =
			case+ e of
			| ~pat_symbol(_) => ()
			| ~pat_atom(_) => ()
			| ~pat_mult(_) => ()
	in
		list_vt_freelin<Pat>(pat)
	end

fn pattern_print(pat: !Pat): void =
	case+ pat of
	| pat_symbol(s) => print(s)
	| pat_atom(s) => (print("?"); print(s))
	| pat_mult(s) => (print("*"); print(s))

fn skeleton_print(ske: !Ske): void =
	case+ ske of
	| ske_symbol(s) => print(s)
	| ske_hole(s) => (print(":"); print(s))

overload print with pattern_print
overload print with skeleton_print

// TODO why doesnt ATS like my print implementations?????
fun pattern_list_print(pat: !Pattern): void =
	case+ pat of
	| list_vt_cons(p, ps) => (print(p); print(" "); pattern_list_print(ps))
	| list_vt_nil() => ()


fun skeleton_list_print(ske: !Skeleton): void = 
	case+ ske of
	| list_vt_cons(s, ss) => (print(s); print(" "); skeleton_list_print(ss))
	| list_vt_nil() => ()


// overload fprint with pattern_list_print

fun expression_free(exp: Expression): void = list_vt_free(exp)


#define :: list_vt_cons

viewtypedef dict(n: int) = [n: int] list_vt(@(string, Expression), n)
viewtypedef Dict = [n: int] dict(n)

(*
fun what(l: List_vt(int), l2: Option_vt(char)): void = 
	case+ l of
	| ~list_vt_cons(_, xs) => what(xs, l2)
	| ~list_vt_nil() => option_vt_free(l2)//???????????????????????????????????????????????????
*)

fun expression_new(): Expression = list_vt_nil()

fun dictionary_new(): Dict = list_vt_nil()

fun dictionary_free(dict: Dict): void = 
	case+ dict of
	| ~list_vt_nil() => ()
	| ~(_, def) :: xs => (
		free(def);
		dictionary_free(xs)
	)

fun dictionary_print(dict: !Dict): void = 
	case+ dict of
	| list_vt_nil() => ()
	| x :: xs => (
		print!(x.0, " = ");
		print_list_vt<string>(x.1);
		//list_vt_free(def);
		println!();
		dictionary_print(xs)
	)

fun lookup(symbol: string, dict: !Dict): Option_vt(Expression) =
	case+ dict of
	| list_vt_cons(x, ds) when strcmp(x.0, symbol) = 0 =>
		Some_vt(list_vt_copy(x.1))
	| list_vt_cons(_, ds) => lookup(symbol, ds)
	| list_vt_nil() => None_vt()


fun skeleton_free(ske: Skeleton): void =
	let
		implement list_vt_freelin$clear<Ske>(s) =
			case+ s of
			| ~ske_symbol(_) => ()
			| ~ske_hole(_) => ()
	in
		list_vt_freelin<Ske>(ske)
	end

fun match(pat: !Pattern, exp: !Expression): Option_vt(Dict) =
	let
		val dict = dictionary_new();
		val temp = $list_vt{string}();

		fun loop(pat: !Pattern, exp: !Expression, dict: Dict, temp: Expression): Option_vt(Dict) = 
			case+ (pat, exp) of
			| (pat_symbol(s1)::ps, s2::es) when strcmp(s1, s2) = 0 => loop(ps, es, dict, temp) where {
				// XXX ????? why am I extending the dictionary here anyways
				// val dict' = list_vt_extend(dict, (s1, s2 :: list_vt_nil))
			}
			| (pat_symbol(s1)::ps, s2::es) => (
				dictionary_free(dict);
				list_vt_free(temp);
				None_vt()
			)
			| (pat_atom(s1)::ps, s2::es) => loop(ps, es, dict', temp) where {
				val dict' = list_vt_extend(dict, (s1, s2 :: list_vt_nil))
			}
			// PATTERN: some thing *what ever => ...  |||| and the expression is empty, dont match
			| (pat_mult(s1)::_, list_vt_nil()) => (
				list_vt_free(temp);
				Some_vt(dict)
			)
			// PATTERN: some thing *end => ...
			| (pat_mult(s1)::list_vt_nil(), _) => Some_vt(dict') where {
				val () = list_vt_free(temp)
				val dict' = list_vt_extend(dict, (s1, list_vt_copy(exp)))
			}
			// PATTERN: some thing *alot end => ...
			| (pat_mult(s1)::pat_symbol(lookahead)::ps, s2::es) when strcmp(lookahead, s2) = 0 => 
			let
				val what = list_vt_copy(temp)
				val () = list_vt_free(temp)
				val temp = $list_vt{string}()
				val dict' = list_vt_extend(dict, (s1, what))
			in
				loop(ps, es, dict', temp)
			end

			| (pat_mult(s1)::pat_symbol(lookahead)::ps, s2::es) => 
			let
				// XXX this used to be extend
				// val tmp = list_vt_append(temp, s2::list_vt_nil())
				val tmp = list_vt_extend(temp, s2)
			in
				loop(pat, es, dict, tmp)
			end
			// TODO maybe not?	
			| (list_vt_nil(), _) => (
				list_vt_free(temp);
				Some_vt(dict)
			)
			
			| (_, _) => (
				// Lets try to be positive
				// dictionary_free(dict);
				list_vt_free(temp);
				Some_vt(dict)
			)

	in
		loop(pat, exp, dict, temp)
	end


fun instantiate(ske: !Skeleton, dict: !Dict): Option_vt(Expression) =
	let
		val exp: Expression = expression_new()
		fun loop(ske: !Skeleton, dict: !Dict, exp: Expression): Option_vt(Expression) =
			case+ ske of
			| ske_symbol(s)::ss => loop(ss, dict, exp') where {
				// XXX this used to be extend
				val exp' = list_vt_append(s::list_vt_nil, exp)
			}
			| ske_hole(s)::ss => (
				case+ lookup(s, dict) of
				// TODO way too many (two, to be exact) reverses
				| ~Some_vt(def) => loop(ss, dict, list_vt_append(list_vt_reverse(def), exp))
				| ~None_vt() => (
					free(exp);
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

// overload free with option_vt_free


// REPL
implement main0(argc, argv) =
	let
		fun loop(): void = 
			let
				val line = fileref_get_line_string(stdin_ref)
			in
				println!(line);
				free(line);
				loop()
			end
			
	in
		loop()
	end
