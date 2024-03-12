import cbor
from pprint import pprint
import sys
import time

cbor_path, = sys.argv[1:]

c = cbor.load(open(cbor_path, 'rb'))

cap = 65536
assert len(c) <= cap

TAG_CONST = 0
TAG_VAR = 1
TAG_NOT = 2
TAG_BINARY = 3
TAG_MUX = 4

POINTER_INDICES_FOR_TAG = {
        TAG_CONST: (),
        TAG_VAR: (),
        TAG_NOT: (0),
        TAG_BINARY: (1, 2),
        TAG_MUX: (0, 1, 2),
        }

print('// AUTOMATICALLY GENERATED by %s at %s' % (sys.argv[0], time.asctime(time.localtime())))
print()

print('use cheesecloth_sym_proof_secret_decls::{TERM_TABLE_CAPACITY, RawTermKind};')

print()
print('#[no_mangle]')
print('#[link_section = ".rodata.secret"]')
print('pub static TERM_TABLE: [RawTermKind; TERM_TABLE_CAPACITY] = [')
for i, t in enumerate(c):
    raw_args = [t['x'], t['y'], t['z']]
    args = ['%d as *const u8' % x for x in raw_args]
    for j in POINTER_INDICES_FOR_TAG[t['tag']]:
        assert raw_args[j] < i
        args[j] = '&TERM_TABLE[%d] as *const RawTermKind as *const u8' % raw_args[j]
    fields = [
            ('tag', t['tag']),
            ('x', args[0]),
            ('y', args[1]),
            ('z', args[2]),
            ]
    print('  RawTermKind { %s },' % ', '.join('%s: %s' % (k, v) for k,v in fields))
for i in range(len(c), cap):
    fields = [
            ('tag', '0'),
            ('x', '0 as *const u8'),
            ('y', '0 as *const u8'),
            ('z', '0 as *const u8'),
            ]
    print('  RawTermKind { %s },' % ', '.join('%s: %s' % (k, v) for k,v in fields))
print('];')

print()
print('#[no_mangle]')
print('#[link_section = ".rodata.secret"]')
print('pub static TERM_TABLE_LEN: usize = %d;' % len(c))
