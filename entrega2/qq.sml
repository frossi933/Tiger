val r = {a=1, b=ref 1};
val _ = (#b(r)) := 15
val x = !(#b(r))

fun f(R as {a, b=ref _}) = (#b(R) := 155; R)

