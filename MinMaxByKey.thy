theory MinMaxByKey
  imports Main
begin

definition min_by_key1 :: "('a \<Rightarrow> ('b :: linorder)) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a" where
  "min_by_key1 f x xs \<equiv>
    fold (\<lambda>acc. \<lambda>x. if f x < f acc then x else acc) xs x"

primrec min_by_key :: "('a \<Rightarrow> ('b :: linorder)) \<Rightarrow> 'a list \<Rightarrow> 'a option" where
  "min_by_key f [] = None" |
  "min_by_key f (x # xs) = Some (min_by_key1 f x xs)"

definition max_by_key1 :: "('a \<Rightarrow> ('b :: linorder)) \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a" where
  "max_by_key1 f x xs \<equiv>
    fold (\<lambda>acc. \<lambda>x. if f x \<ge> f acc then x else acc) xs x"

primrec max_by_key :: "('a \<Rightarrow> ('b :: linorder)) \<Rightarrow> 'a list \<Rightarrow> 'a option" where
  "max_by_key f [] = None" |
  "max_by_key f (x # xs) = Some (max_by_key1 f x xs)"

lemma max_by_key1_first:
  "f x \<le> f (max_by_key1 f x xs)"
  apply (induct xs arbitrary: x)
   apply (fastforce simp: max_by_key1_def)
  apply (clarsimp simp: max_by_key1_def)
  apply (meson le_cases order_trans)
  done

lemma max_by_key1_le:
  "x \<in> set (y # ys) \<Longrightarrow>
   f x \<le> f (max_by_key1 f y ys)"
  apply clarsimp
  apply (erule disjE)
   apply (fastforce intro: max_by_key1_first)
  apply (induct ys arbitrary: x y)
   apply fastforce
  apply (rename_tac y' ys')
  apply clarsimp
  apply (erule disjE)
   apply (clarsimp simp: max_by_key1_def)
   apply (rule conjI)
    apply clarsimp
    apply (erule order_trans)
    apply (fastforce intro: max_by_key1_first[simplified max_by_key1_def])
   apply (fastforce intro: max_by_key1_first[simplified max_by_key1_def])
  apply (fastforce simp: max_by_key1_def)
  done

lemma max_by_key_le:
  "xs \<noteq> [] \<Longrightarrow>
   x \<in> set xs \<Longrightarrow>
   f x \<le> f (the (max_by_key f xs))"
  by (case_tac xs; fastforce simp: max_by_key_def max_by_key1_le)

lemma max_by_key1_elem:
  "m = max_by_key1 f x xs \<Longrightarrow>
   all = x # xs \<Longrightarrow>
   m \<in> set all"
  apply clarsimp
  apply (induct xs arbitrary: m x all)
   apply (fastforce simp: max_by_key1_def)
  apply (fastforce simp: max_by_key1_def)
  done

lemma max_by_key_elem:
  "xs \<noteq> [] \<Longrightarrow>
   the (max_by_key f xs) \<in> set xs"
  apply (cases xs)
   apply fastforce
  apply (fastforce intro: max_by_key1_elem)
  done

lemma max_by_key_rec:
  "max_by_key f xs = res \<Longrightarrow>
   (\<exists>z. res = Some z \<and> (\<forall>x \<in> set xs. f x \<le> f z)) \<or> res = None"
  apply (case_tac xs)
   apply fastforce
  apply clarsimp
  apply (fastforce intro: max_by_key1_le max_by_key1_first)
  done

end