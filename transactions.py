from collections import defaultdict
from dataclasses import dataclass
from typing import Dict, List, Iterable, Optional, Set, Tuple
from enum import auto, Enum


@dataclass(frozen=True)
class Operation:
    initiator: str


@dataclass(frozen=True)
class Write(Operation):
    target: str


@dataclass(frozen=True)
class Read(Operation):
    target: str


@dataclass(frozen=True)
class GetSharedLock(Operation):
    target: str


@dataclass(frozen=True)
class GetExclusiveLock(Operation):
    target: str


@dataclass(frozen=True)
class ReleaseLocks(Operation):
    targets: Tuple[str, ...]


@dataclass(frozen=True)
class DenyLock(Operation):
    target: str


@dataclass(frozen=True)
class EndOfTransaction(Operation):
    pass


class TransactionParser():
    _input: str
    _next_ch_idx: int
    _ops: List[Operation]
    

    def __init__(self, input_text):
        self._input = input_text
        self._reset_state()


    def _reset_state(self):
        self._next_ch_idx = 0
        self._ops = []


    def _parse(self) -> List[Operation]:
        self._reset_state()
        self._parse_ops()
        return self._ops


    def _parse_ops(self):
        while not self._no_more_input():
            self._consume_spaces()
            op = self._parse_op()
            self._consume_spaces()
            self._assert_next_ch_or_eof(',;')
            self._ops.append(op)
        

    def _parse_op(self) -> Operation:
        op_str = self._parse_op_str()
        initiator = self._parse_initiator()
        if op_str == 'W':
            return self._parse_write_cont(initiator)
        elif op_str == 'R':
            return self._parse_read_cont(initiator)
        elif op_str == 'S':
            return self._parse_get_shared_lock_cont(initiator)
        elif op_str == 'X':
            return self._parse_get_exclusive_lock_cont(initiator)
        elif op_str == 'REL':
            return self._parse_release_locks_cont(initiator)
        elif op_str == 'DENIED':
            return self._parse_deny_lock(initiator)
        else:
            raise RuntimeError(f'Unknown operation type: [{op_str}]')


    def _no_more_input(self):
        return self._next_ch_idx >= len(self._input)


    def _consume_spaces(self):
        self._parse_str_until_eof_or(lambda ch: not ch.isspace())


    def _next_ch(self) -> Optional[str]:
        next_ch = self._peek_ch()
        if next_ch is None:
            return None
        else:
            self._next_ch_idx += 1
            return next_ch


    def _assert_next_ch_or_eof(self, expect_chs: str) -> Optional[str]:
        next_ch = self._peek_ch()
        if next_ch is None:
            return None
        elif next_ch not in expect_chs:
            raise RuntimeError(f'Expected a character in [{expect_chs}], but got [{next_ch}]')
        else:
            self._next_ch_idx += 1
            return next_ch


    def _assert_next_ch(self, expect_chs) -> str:
        next_ch = self._assert_next_ch_or_eof(expect_chs)
        if next_ch is None:
            raise RuntimeError(f'Expected a character in [{expect_ch}], but there is no more input')
        else:
            return next_ch


    def _peek_ch(self) -> Optional[str]:
        if self._no_more_input():
            return None
        else:
            next_ch = self._input[self._next_ch_idx]
            return next_ch


    def _parse_str_until_eof_or(self, pred) -> Optional[str]:
        chars = []
        next_ch = self._peek_ch()
        while next_ch is not None and not pred(next_ch):
            self._next_ch()
            chars.append(next_ch)
            next_ch = self._peek_ch()
        return None if next_ch is None else ''.join(chars)


    def _parse_str_until(self, pred) -> str:
        s = self._parse_str_until_eof_or(pred)
        if s is None:
            raise RuntimeError('Expect more inputs')
        else:
            return s


    def _parse_op_str(self) -> str:
        return self._parse_str_until(lambda ch: ch.isdigit())
        

    def _parse_initiator(self) -> str:
        return self._parse_str_until(lambda ch: not ch.isdigit())


    def _parse_targets(self) -> List[str]:
        self._assert_next_ch('(')
        comma_seperated_targets = self._parse_str_until(lambda ch: ch == ')')
        self._assert_next_ch(')')
        return comma_seperated_targets.replace(' ', '').split(',')


    def _parse_one_target(self) -> str:
        targets = self._parse_targets()
        targets_len = len(targets)
        if targets_len != 1:
            raise RuntimeError('Expect 1 target, but got {targets_len}')
        else:
            return targets[0]

        
    def _parse_write_cont(self, initiator):
        target = self._parse_one_target()
        op = Write(initiator=initiator, target=target)
        return op


    def _parse_read_cont(self, initiator):
        target = self._parse_one_target()
        op = Read(initiator=initiator, target=target)
        return op


    def _parse_get_shared_lock_cont(self, initiator):
        target = self._parse_one_target()
        op = GetSharedLock(initiator=initiator, target=target)
        return op


    def _parse_get_exclusive_lock_cont(self, initiator):
        target = self._parse_one_target()
        op = GetExclusiveLock(initiator=initiator, target=target)
        return op


    def _parse_release_locks_cont(self, initiator):
        targets = self._parse_targets()
        op = ReleaseLocks(initiator=initiator, targets=tuple(targets))
        return op


    def _parse_deny_lock(self, initiator):
        target = self._parse_one_target()
        op = DenyLock(initiator=initiator, target=target)
        return op


    @staticmethod
    def parse(input_text) -> Iterable[Operation]:
        return TransactionParser(input_text)._parse()


class LockType(Enum):
    SHARED    = auto()
    EXCLUSIVE = auto()


class LockManager():
    _shared_locks: Dict[str, Set[str]]
    _exclusive_locks: Dict[str, str]
    _initiator_to_locks_map: Dict[str, Dict[str, LockType]]


    def __init__(self):
        self._shared_locks = defaultdict(set)
        self._exclusive_locks = {}
        self._initiator_to_locks_map = defaultdict(dict)

    
    # return True on success
    def add_shared_lock(self, initiator, target) -> bool:
        if target in self._exclusive_locks:
            owner = self._exclusive_locks[target]
            # raise RuntimeError(f'[add_shared_lock] {owner} owns exclusive lock on {target}')
            return False
        else:
            self._shared_locks[target].add(initiator)
            self._initiator_to_locks_map[initiator][target] = LockType.SHARED
            return True


    # return True on success
    def add_exclusive_lock(self, initiator, target) -> bool:
        if target in self._exclusive_locks:
            owner = self._exclusive_locks[target]
            # raise RuntimeError(f'[add_exclusive_lock] {owner} owns exclusive lock on {target}')
            return False
        if target in self._shared_locks:
            owners = self._shared_locks[target]
            if len(owners) > 1:
                return False
            if len(owners) == 1:
                if initiator in owners:
                    self.release_lock(initiator, target)
                else:
                    return False
        self._initiator_to_locks_map[initiator][target] = LockType.EXCLUSIVE
        self._exclusive_locks[target] = initiator
        return True


    def get_lock(self, initiator, target) -> Optional[LockType]:
        lock_map = self._initiator_to_locks_map[initiator]
        return lock_map[target] if target in lock_map else None


    def release_lock(self, initiator, target):
        lock_type = self._initiator_to_locks_map[initiator][target]
        del self._initiator_to_locks_map[initiator][target]
        if lock_type == LockType.SHARED:
            self._shared_locks[target].remove(initiator)
        elif lock_type == LockType.EXCLUSIVE:
            del self._exclusive_locks[target]


    def release_all_locks(self, initiator) -> Iterable[str]:
        locks_map = self._initiator_to_locks_map[initiator]
        all_targets = locks_map.keys()

        for target, _ in list(locks_map.items()):
            self.release_lock(initiator, target)
        return all_targets


class IsolationLevel(Enum):
    READ_COMMITTED  = auto()
    REPEATABLE_READ = auto()
    

def _add_in_end_of_transactions(ops: Iterable[Operation]) -> Iterable[Operation]:
    last_op_idx_map = {} # maps initiator to index
    for idx, op in enumerate(ops):
        last_op_idx_map[op.initiator] = idx

    new_ops = []
    for idx, op in enumerate(ops):
        new_ops.append(op)
        last_op_idx = last_op_idx_map[op.initiator]
        if idx == last_op_idx:
            new_ops.append(EndOfTransaction(op.initiator))
    return new_ops


def _augment_read(
    read: Read, lock_manager: LockManager, policy: Dict[str, IsolationLevel]
) -> (Iterable[Operation], bool): # bool indicates whether a lock was denied
    new_ops = []
    if (lock_manager.get_lock(read.initiator, read.target) is None):
        if not lock_manager.add_shared_lock(read.initiator, read.target):
            new_ops.append(DenyLock(read.initiator, read.target))
            return (new_ops, True)
        else:
            new_ops.append(GetSharedLock(read.initiator, read.target))
    new_ops.append(read)

    iso_level = policy[read.initiator]
    if iso_level == IsolationLevel.READ_COMMITTED:
        lock_manager.release_lock(read.initiator, read.target)
        locks = (read.target,)
        new_ops.append(ReleaseLocks(read.initiator, locks))
    return (new_ops, False)


def _augment_write(
    write: Write, lock_manager: LockManager
) -> (Iterable[Operation], bool): # bool indicates whether a lock was denied
    new_ops = []
    if lock_manager.get_lock(write.initiator, write.target) != LockType.EXCLUSIVE:
        if not lock_manager.add_exclusive_lock(write.initiator, write.target):
            new_ops.append(DenyLock(write.initiator, write.target))
            return (new_ops, True)
        else:
            new_ops.append(GetExclusiveLock(write.initiator, write.target))
    new_ops.append(write)
    return (new_ops, False)


def _augment_op(
    op: Operation, lock_manager: LockManager, policy: Dict[str, IsolationLevel]
) -> (Iterable[Operation], bool): # bool indicates whether a lock was denied
    if isinstance(op, Read):
        return _augment_read(op, lock_manager, policy)

    elif isinstance(op, Write):
        return _augment_write(op, lock_manager)

    elif isinstance(op, EndOfTransaction):
        locks = lock_manager.release_all_locks(op.initiator)
        new_ops = []
        new_ops.append(ReleaseLocks(op.initiator, locks))
        new_ops.append(op)
        return (new_ops, False)


def complete_transaction(
    ops: Iterable[Operation], policy: Dict[str, IsolationLevel]
) -> Iterable[Operation]:
    ops = _add_in_end_of_transactions(ops)
    lock_manager = LockManager()
    new_ops = []

    for op in ops:
        augmented_ops, lock_denied = _augment_op(op, lock_manager, policy)
        new_ops.extend(augmented_ops)
        if lock_denied:
            break
    return new_ops


def deserialize_ops(ops: Iterable[Operation]) -> str:
    s = []
    for op in ops:
        if isinstance(op, Write):
            s.append(f'W{op.initiator}({op.target})')

        elif isinstance(op, Read):
            s.append(f'R{op.initiator}({op.target})')

        elif isinstance(op, GetSharedLock):
            s.append(f'S{op.initiator}({op.target})')

        elif isinstance(op, GetExclusiveLock):
            s.append(f'X{op.initiator}({op.target})')

        elif isinstance(op, ReleaseLocks):
            locks = ','.join(op.targets)
            s.append(f'REL{op.initiator}({locks})')

        elif isinstance(op, DenyLock):
            s.append(f'DENIED{op.initiator}({op.target})')

        elif isinstance(op, EndOfTransaction):
            # NOTE ignored, it's for internal convenience only
            pass
    return '; '.join(s)


if __name__ == '__main__':
    s = 'R1(B), W1(B), R2(A), W2(B), R1(C)'
    ops = TransactionParser.parse(s)
    policy = {
        '1': IsolationLevel.READ_COMMITTED,
        '2': IsolationLevel.READ_COMMITTED,
    }
    new_ops = complete_transaction(ops, policy)
    for op in new_ops:
        print(op)
    s = deserialize_ops(new_ops)
    print('------------')
    print(s)