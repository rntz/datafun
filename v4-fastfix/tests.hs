import Runtime

-- Transitive closure, seminaively.
trans :: Ord a => Set (a,a) -> Set (a,a)
trans edge_9 = (fastfix ((\path_8 -> (union edge_9 (forIn edge_9 (\a_2 -> (let da_2 = ((), ()) in (forIn path_8 (\b_3 -> (let db_3 = ((), ()) in (guard ((snd a_2) == (fst b_3)) (set [((fst a_2), (snd b_3))])))))))))), (\path_8 -> (\dpath_8 -> (forIn edge_9 (\a_2 -> (let da_2 = ((), ()) in (forIn dpath_8 (\b_3 -> (let db_3 = ((), ()) in (guard ((snd a_2) == (fst b_3)) (set [((fst a_2), (snd b_3))]))))))))))))
