
# DATA DEFINITIONS
# - A Relation (R) is a [Set X]
# - A Functional Dependency (FD) is a [Tuple [Set X] [Set X]]
#   where len(lhs) > 0, len(rhs) > 0, lhs ∩ rhs = ∅
# - A Singleton Functional Dependency (SFD) is FD 
#   where len(rhs) = 1


def powerset(init_elems):
    # [Iterable X] -> [Iterable [Set X]]

    def go(s):
        if len(s) == 0:
            return [set()]
        else:
            x = s.pop()
            result = go(s)
            result_with_x_added = list(map(lambda elems: elems.union([x]), result))
            result.extend(result_with_x_added)
            return result

    s = set(init_elems)
    return go(s)


def get_keys(relation, fds):
    # R [Iterable FD] -> [Iterable [Set X]]

    lhs_elems, rhs_elems = set(), set()
    for lhs, rhs in fds:
        lhs_elems.update(lhs)
        rhs_elems.update(rhs)

    middle_elems = lhs_elems.intersection(rhs_elems)
    lhs_elems = lhs_elems.difference(middle_elems)
    rhs_elems = rhs_elems.difference(middle_elems)
    # essentially lhs_elems + none_elems
    minimal_key = relation.difference(middle_elems).difference(rhs_elems)

    keys = []
    ordered_middle_elems_powerset = sorted(powerset(middle_elems), key=len, reverse=True)
    while len(ordered_middle_elems_powerset) > 0:
        min_set = ordered_middle_elems_powerset.pop()
        key_suspect = minimal_key.union(min_set)
        key_suspect_closure = get_nontrivial_closure_of(key_suspect, fds)
        if key_suspect_closure.union(key_suspect) == relation:
            keys.append(key_suspect)
            ordered_middle_elems_powerset = list(
                filter(lambda s: not min_set.issubset(s), ordered_middle_elems_powerset)
            )

    return keys


def get_violating_fds(relation, fds):
    keys = get_keys(relation, fds)

    def is_superkey(elems):
        return any(map(lambda key: key.issubset(lhs), keys))

    def is_violating_fd(fd):
        lhs, _ = fd
        return not is_superkey(lhs)

    return list(filter(is_violating_fd, fds))


def get_fd_with_largest_rhs(fds):
    # input may be empty, in which case output is `None`
    largest_rhs_cardinality = 0
    fd_with_largest_rhs = None
    for _, rhs in fds:
        if len(rhs) > largest_rhs_cardinality:
            largest_rhs_cardinality = len(rhs)
            fd_with_largest_rhs = rhs
    return fd_with_largest_rhs


def fds_to_sfds(fds):
    # [Iterable FD] -> [Iterable SFD]
    sfds = []
    for lhs, rhs in fds:
        for x in rhs:
            sfd = (set(lhs), set([x]))
            sfds.append(sfd)
    return sfds


def merge_rhs_in_fds(sfds):
    # [Iterable SFD] -> [Iterable FD]
    lhs_to_rhs = {} # [Map FrozenSet Set]
    for lhs, rhs in sfds:
        lhs_fs = frozenset(lhs)
        if lhs_fs in lhs_to_rhs:
            lhs_to_rhs[lhs_fs].update(rhs)
        else:
            lhs_to_rhs[lhs_fs] = set(rhs)
    fds = [(lhs, rhs) for lhs, rhs in lhs_to_rhs.items()]
    return fds


def get_minimal_cover(fds):
    sfds = fds_to_sfds(fds)

    def reduce_sfds_lhs_until_fixpoint():
        changed = False
        for lhs, rhs in sfds:
            if len(lhs) <= 1: # should never be 0
                continue
            lhs_list = list(lhs)
            for idx, x in enumerate(lhs):
                reduced_lhs = lhs_list[:idx] + lhs_list[idx+1:]
                reduced_lhs_closure = get_nontrivial_closure_of(reduced_lhs, fds)
                if rhs.issubset(reduced_lhs_closure):
                    changed = True
                    lhs.remove(x)
                    break
        if changed:
            reduce_sfds_lhs_until_fixpoint()

    def reduce_sfds_until_fixpoint(init_sfds):
        def go(sfds, idx):
            # 1. tries to remove `sfds[idx]`
            # 2. regardless of whether (1) had effect, tries `idx-1` next
            if idx < 0:
                return sfds
            reduced_sfds = sfds[:idx] + sfds[idx+1:]
            removed_sfd = sfds[idx]
            removed_sfd_lhs, removed_sfd_rhs = removed_sfd
            removed_sfd_lhs_closure = get_nontrivial_closure_of(removed_sfd_lhs, reduced_sfds)
            if removed_sfd_rhs.issubset(removed_sfd_lhs_closure):
                sfds = reduced_sfds
            return go(sfds, idx - 1)

        return go(init_sfds, len(sfds) - 1)
    

    reduce_sfds_lhs_until_fixpoint()
    sfds = reduce_sfds_until_fixpoint(sfds)
    return merge_rhs_in_fds(sfds)


def get_projected_fds(relation, fds):
    projected_fd_candidates = []
    for s in powerset(relation):
        s_closure = get_nontrivial_closure_of(s, fds)
        projected_s_closure = s_closure.intersection(relation)
        if len(projected_s_closure) > 0:
            projected_fd = (s, projected_s_closure)
            projected_fd_candidates.append(projected_fd)

    projected_fds = get_minimal_cover(projected_fd_candidates)
    return projected_fds


def get_nontrivial_closure_of(elems, fds):
    # ENSURE output ∩ elems = ∅
    # [Iterable X] [Iterable FD] -> [Set X]
    result = set(elems)

    def expand_result_until_fixpoint():
        changed = False
        for lhs, rhs in fds:
            if lhs.issubset(result) and not rhs.issubset(result):
                result.update(rhs)
                changed = True
        if changed:
            expand_result_until_fixpoint()

    expand_result_until_fixpoint()
    return result.difference(elems)


def decompose_impl(init_relation, init_fds):
    # R [Iterable FD] -> [List [Tuple Relation [Iterable FD]]]
    results = []

    def go(relation, fds):
        # put answer into `results`
        violating_fds = get_violating_fds(relation, fds)
        worst_fd = get_fd_with_largest_rhs(violating_fds)
        if worst_fd is None:
            answer = (relation, fds)
            results.append(answer)
            return

        lhs_elems = worst_fd[0]
        violating_fd_relation_rhs = get_nontrivial_closure_of(lhs_elems, fds)
        violating_fd_relation = (lhs_elems, violating_fd_relation_rhs)
        other_relation = relation.difference(violating_fd_relation_rhs)

        def recur(projected_relation):
            projected_relation_fds = get_projected_fds(projected_relation, fds)
            go(projected_relation, projected_relation_fds)

        recur(violating_fd_relation)
        recur(other_relation)

    go(init_relation, init_fds)
    return results


def decompose(relation, raw_fds):
    # [Set X] [Iterable [Tuple [Set X] [Set X]]] ->
    #    [List [Tuple Relation [Iterable FD]]]
    normalized_fds = []
    for lhs, rhs in raw_fds:
        if len(lhs) == 0 or len(rhs) == 0:
            print(f'empty lhs/rhs in raw_fds: {lhs} --> {rhs}')
            exit()
        rhs = lhs.difference(lhs)
        normalized_fd = (lhs, rhs)
        normalized_fds.append(normalized_fd)
    return decompose_impl(relation, normalized_fds)


# ------------------------------------------
# ------------------TESTS-------------------
# ------------------------------------------
def test_get_nontrivial_closure_of():
    elems = set([1])
    fds = [
        (set([1]), set([2])),
        (set([2]), set([3])),
    ]
    result = get_nontrivial_closure_of(elems, fds)
    print(result)


def test_get_keys():
    relation = set([1, 2, 3, 4])
    fds = [
        (set([1]), set([2])),
        (set([2]), set([3])),
    ]
    result = get_keys(relation, fds)
    print(result)


def test_get_minimal_cover():
    # source of algorithm and testcase:
    # https://stackoverflow.com/questions/10284004/minimal-cover-and-functional-dependencies
    fds = [
        (set([1]), set([2])),
        (set([1, 2, 3, 4]), set([5])),
        (set([5, 6]), set([7, 8])),
        (set([1, 3, 4, 6]), set([5, 7])),
    ]
    result = get_minimal_cover(fds)
    print(result)


def test_get_projected_fds():
    relation = list('ADEF')
    fds = [
        (set('AD'), set('BC')),
        (set('B'), set('A')),
        (set('C'), set('E')),
        (set('E'), set('BF')),
    ]
    result = get_projected_fds(relation, fds)
    # expect {E->F, AD->E, E->A}, see lecture slide p10:
    # https://www.prairielearn.org/pl/course_instance/128793/instance_question/155100116/clientFilesQuestion/14-%20DBDesign_BCNF.pdf
    print(result)


# -----------------------------------------
# ------------------MAIN-------------------
# -----------------------------------------
def main():
    init_relation = []
    init_raw_fds = [
    ]
    result = decompose(relation, raw_fds)
    for relation, fds in result:
        # TODO pretty-printing
        print(relation, raw_fds)


if __name__ == '__main__':
    main()