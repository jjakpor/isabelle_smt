theory Words      
  imports Main 
begin

no_notation Groups.times_class.times (infixl "*" 70)


type_synonym 'a word = "'a list"
abbreviation Epsilon::"'a word" ("\<epsilon>") where "Epsilon \<equiv> []" 




(* Basic Operations *)


primrec first:: "'a word \<Rightarrow> 'a word" where
"first \<epsilon> = \<epsilon>"|
"first (a#w) = a#\<epsilon>"

definition at:: "'a word \<Rightarrow> nat \<Rightarrow> 'a word" where "at w i \<equiv> first (drop i w)"


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

lemma prefix_not_shorter[simp]:"(length w) < (length v) \<Longrightarrow> \<not>(is_prefix v w)"
  apply(auto simp add: is_prefix_def)
  done

lemma suffix_not_shorter[simp]:"(length w) < (length v) \<Longrightarrow> \<not>(is_suffix v w)"
  apply(auto simp add: is_suffix_def)
  done


lemma factor_embedding:"fac w s l = u \<Longrightarrow> EX x y. x@u@y = w"
  unfolding fac_def  
  apply (metis append_take_drop_id)
  done

lemma factorization:"w = x@u@y \<Longrightarrow> EX s l. fac w s l = u"
  unfolding fac_def  
  apply (metis append_eq_conv_conj)
  done


primrec contains:: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where
"contains \<epsilon> v = (v = \<epsilon>)" |
"contains (x#u) v = ((is_prefix v (x#u)) \<or> (contains u v))" 



primrec find:: "'a word \<Rightarrow> 'a word \<Rightarrow> nat option" where
"find \<epsilon> v = (if (v = \<epsilon>) then Some 0 else None)"|
"find (a#w) v = (if (is_prefix v (a#w)) then Some 0 else (case (find w v) of Some n \<Rightarrow> Some (Suc n) | None \<Rightarrow> None))"





end





