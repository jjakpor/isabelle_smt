theory Words        
  imports Main
begin

no_notation Groups.times_class.times (infixl "*" 70)


type_synonym 'a word = "'a list"
abbreviation Epsilon::"'a word" ("\<epsilon>") where "Epsilon \<equiv> []" 




(* Basic Operations *)

fun at :: "'a word \<Rightarrow> nat \<Rightarrow> 'a word"
  where 
  "at Epsilon i = Epsilon" |
  "at (a # w) 0 = (a # Epsilon)"|
  "at (a # w) (Suc n) = at w n "


primrec concat_all:: "'a word list \<Rightarrow> 'a word"
  where
  "concat_all [] = Epsilon" |
  "concat_all (w#ws) = w@(concat_all ws)"



(* Basic substring relations *)

definition fac :: "'a word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a word" where "fac w s l = take l (drop s w)"
definition is_prefix:: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where "is_prefix v w = ((take (size v) w) = v)"
definition is_suffix:: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where "is_suffix v w = is_prefix (rev v) (rev w)" 

lemma [simp]:"fac w 0 (size w) = w"
  unfolding fac_def
  apply(auto)
  done

lemma [simp]: "fac Epsilon s l = Epsilon"
  unfolding fac_def
   apply(auto)
  done

lemma [simp]: "length (fac w s 0) = 0"
  apply(auto simp add: fac_def)
  done

lemma factor_embedding:"fac w s l = u \<Longrightarrow> EX x y. x@u@y = w"
  unfolding fac_def  
  apply (metis append_take_drop_id)
  done

lemma factorization:"w = x@u@y \<Longrightarrow> EX s l. fac w s l = u"
  unfolding fac_def  
  apply (metis append_eq_conv_conj)
  done

lemma eq_prefix_equals: "(a . w) = u*v \<longleftrightarrow>
   (u = Epsilon \<and> (a . w) = v \<or> (\<exists>v'. u = (a . v') \<and> w = v'*v))"
  by(cases u) auto

lemma rev_concat [simp]: "rev (w * v) = (rev v) * (rev w)"
  apply(induct_tac w)
   apply(auto simp add: epsilon_neutrality)
  done
 
theorem rev_rev: "\<And> w. rev(rev w) = w"
  apply(induct_tac w)
  apply(auto)
  done



(* Conversion *)
primrec of_list:: "'a list \<Rightarrow> 'a word"
  where
  "of_list [] = Epsilon" |
  "of_list (x#xs) = x . (of_list xs)"


end





