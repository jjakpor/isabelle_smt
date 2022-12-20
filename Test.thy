theory Test      
  imports Words RegEx
begin

(* Trivial Word Equation *)
lemma  "EX x. x = (of_list ''abc'')"
  apply(auto)
  done


(* Word Equation constant RHS *)
lemma  assumes s:"x = (of_list ''a'') \<and> y = (of_list ''c'')" shows "x * (of_list ''b'')  * y = (of_list ''abc'')"
  apply(simp add: s)
  done

(* Word Equation with two patterns *)
lemma  assumes s:"x = (of_list ''b'') \<and> y = (of_list ''c'')" shows "x * (of_list ''b'')  * y = x*x*y"
  apply(simp add: s)
  done

(* Word Equation with two patterns *)
lemma  assumes s:"x = (of_list ''b'') \<and> y = (of_list ''c'') \<and> z = (of_list ''cc'')" shows "x * (of_list ''b'')  * y = x*x*y \<and> y*y*(of_list ''b'')=z*x"
  apply(simp add: s)
  done

(* Regular Memberships *)

lemma  assumes s:"x = (of_list ''abc'')" shows "x \<in> (Const (of_list ''abc''))"
  apply(simp add: s)
  done

lemma  assumes s:"x = (of_list ''abc'')" shows "x \<in> (Concat (Union (Const (of_list ''a''))(Const (of_list ''c'')))  (Const (of_list ''bc'')))"
  apply(auto simp add: s)
  done

lemma  assumes s:"x = (of_list ''abbbbbc'')" shows "x \<in> (Concat (Const (of_list ''a'')) (Concat (Star (Const (of_list ''b''))) (Const (of_list ''c''))))"
  apply(simp add: s)
  done

lemma  assumes s:"x = (of_list ''abdbbbbc'')" shows "\<not>x \<in> (Concat (Const (of_list ''a'')) (Concat (Star (Const (of_list ''b''))) (Const (of_list ''c''))))"
  apply(simp add: s)
  done

end