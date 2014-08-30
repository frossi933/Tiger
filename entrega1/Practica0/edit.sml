load "Process";
local
    val ed = ref "gedit"
    val a = ref ""
in
    fun seted e = ed:=e
    fun ed s = (if s<>"" then a:=s else ();
               Process.system(!ed^" "^(!a));
               use(!a))
end
