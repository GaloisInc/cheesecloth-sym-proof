import cbor
from pprint import pprint
import sys

cbor_path, = sys.argv[1:]

c = cbor.load(open(cbor_path, 'rb'))
ver, feat, ex = c
ver = tuple(ver)
feat = set(feat)

has_code_segments = ver >= (0, 1, 7, 0) or 'code-segments' in feat
assert has_code_segments, 'support for traces without code-segments is NYI'

prog = ex['program']

OPCODE_TABLE = {
        'and': 'Opcode::Binary(BinOp::And)',
        'or': 'Opcode::Binary(BinOp::Or)',
        'xor': 'Opcode::Binary(BinOp::Xor)',
        'not': 'Opcode::Not',
        'add': 'Opcode::Binary(BinOp::Add)',
        'sub': 'Opcode::Binary(BinOp::Sub)',
        'mull': 'Opcode::Binary(BinOp::Mull)',
        'umulh': 'Opcode::Binary(BinOp::Umulh)',
        'smulh': 'Opcode::Binary(BinOp::Smulh)',
        'udiv': 'Opcode::Binary(BinOp::Udiv)',
        'umod': 'Opcode::Binary(BinOp::Umod)',
        'shl': 'Opcode::Binary(BinOp::Shl)',
        'shr': 'Opcode::Binary(BinOp::Shr)',
        'cmpe': 'Opcode::Binary(BinOp::Cmpe)',
        'cmpa': 'Opcode::Binary(BinOp::Cmpa)',
        'cmpae': 'Opcode::Binary(BinOp::Cmpae)',
        'cmpg': 'Opcode::Binary(BinOp::Cmpg)',
        'cmpge': 'Opcode::Binary(BinOp::Cmpge)',
        'mov': 'Opcode::Mov',
        'cmov': 'Opcode::Cmov',
        'jmp': 'Opcode::Jmp',
        'cjmp': 'Opcode::Cjmp',
        'cnjmp': 'Opcode::Cnjmp',
        'store1': 'Opcode::Store(MemWidth::W1)',
        'store2': 'Opcode::Store(MemWidth::W2)',
        'store4': 'Opcode::Store(MemWidth::W4)',
        'store8': 'Opcode::Store(MemWidth::W8)',
        'load1': 'Opcode::Load(MemWidth::W1)',
        'load2': 'Opcode::Load(MemWidth::W2)',
        'load4': 'Opcode::Load(MemWidth::W4)',
        'load8': 'Opcode::Load(MemWidth::W8)',
        'poison8': 'Opcode::Poison(MemWidth::W8)',
        'answer': 'Opcode::Answer',
        'advise': 'Opcode::Advise',
        }

def convert_instr(instr):
    op, rd, r1, imm, op2 = instr
    fields = [
            ('opcode', OPCODE_TABLE[op]),
            ('rd', str(rd or 0)),
            ('r1', str(r1 or 0)),
            ('op2', 'Operand::%s(%d)' % ('Imm' if imm else 'Reg', op2)),
            ]
    return 'Instr { %s }' % ', '.join('%s: %s' % (k, v) for k,v in fields)

prog_instrs = []
prog_chunks = []

for cs in prog:
    assert not cs['secret'], 'secret code segments are not supported'
    fields = [
            ('start_addr', cs['addr']),
            ('start_index', len(prog_instrs)),
            ('len', cs['len']),
            ]
    assert len(cs['instrs']) <= cs['len']
    for instr in cs['instrs']:
        prog_instrs.append(convert_instr(instr))
    for i in range(len(cs['instrs']), cs['len']):
        prog_instrs.append(convert_instr(('answer', 0, 0, 0, True)))

    prog_chunks.append('ProgramChunk { %s }' % ', '.join('%s: %s' % (k, v) for k,v in fields))

print('use sym_proof::BinOp;')
print('use sym_proof::micro_ram::{Instr, Operand, Opcode, MemWidth, ProgramChunk};')

print()
print('pub static PROG_INSTRS: [Instr; %d] = [' % len(prog_instrs))
for instr in prog_instrs:
    print('  %s,' % instr)
print('];')

print()
print('pub static PROG_CHUNKS: [ProgramChunk; %d] = [' % len(prog_chunks))
for chunk in prog_chunks:
    print('  %s,' % chunk)
print('];')

