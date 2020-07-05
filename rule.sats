staload "./pattern.sats"
staload "./skeleton.sats"
staload "./string.sats"

viewtypedef Rule = @{
	level = int,
	precedence = int,
	name = String,
	pattern = Pattern,
	skeleton = Skeleton
}

fn rule_is_valid(!Rule): bool
fn rule_copy(!Rule): Rule
fn rule_print(!Rule): void
fn rule_free(Rule): void

overload gcopy with rule_copy
overload gprint with rule_print
overload gfree with rule_free
