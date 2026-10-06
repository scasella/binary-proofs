#!/usr/bin/env python3
"""Trusted final ELF/image extraction; GNU cross-checks are identity evidence, not proof."""
import hashlib, importlib.util, json, re, struct, sys
from pathlib import Path
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
BUILT=HERE/'compiled-v1'
BIAS=0x23000000
PARSER_SHA='6f35da09dea20999a64f5698618b369822c3eac60ebe7d6b161021206f163cff'
sha=lambda data:hashlib.sha256(data).hexdigest()
parser=ROOT/'scripts/inventory.py'
assert sha(parser.read_bytes())==PARSER_SHA
spec=importlib.util.spec_from_file_location('c3_pinned_elf',parser)
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
elf=module.ELF(BUILT/'c3.so');assert elf.type==3 and elf.machine==62
symbol,=[s for s in elf.symbols if s['table']=='.dynsym' and s['name']=='c3_compare_clear_compare']
entry=symbol['vaddr'];offset,code=elf.extract(entry,symbol['size']);rows=[]
for line in (BUILT/'disassembly.txt').read_text().splitlines():
 fields=line.split('\t')
 if len(fields)<3:continue
 match=re.fullmatch(r'\s*([0-9a-f]+):',fields[0])
 if not match:continue
 va=int(match[1],16)
 if not entry<=va<entry+len(code):continue
 raw=bytes.fromhex(fields[1]);assert code[va-entry:va-entry+len(raw)]==raw
 parts=fields[2].strip().split(None,1)
 rows.append(dict(elf_vaddr=va,loaded_address=BIAS+va,offset=va-entry,size=len(raw),bytes_hex=raw.hex(),mnemonic=parts[0],operands=parts[1] if len(parts)>1 else ''))
assert sum(r['size'] for r in rows)==len(code)
expected=['push','push','push','push','sub','mov','mov','mov','call','xor','test','sete','mov','mov','call','mov','mov','mov','call','test','je','test','sete','movzx','jmp','mov','add','pop','pop','pop','pop','ret']
assert [r['mnemonic'] for r in rows]==expected
links=[]
for call,name,target in zip([r for r in rows if r['mnemonic']=='call'],['CRYPTO_memcmp','OPENSSL_cleanse','CRYPTO_memcmp'],[0x10241840,0x102417d0,0x10241840]):
 raw=bytes.fromhex(call['bytes_hex']);assert len(raw)==5 and raw[0]==0xe8
 disp=struct.unpack_from('<i',raw,1)[0];cont=call['elf_vaddr']+5;pv=cont+disp;po,plt=elf.extract(pv,16)
 assert plt[:2]==b'\xff\x25';pd=struct.unpack_from('<i',plt,2)[0];gv=pv+6+pd
 reloc,=[r for r in elf.relocations if r['offset']==gv]
 imported,=[s for s in elf.symbols if s['table']=='.dynsym' and s['name']==name]
 assert reloc['type']==7 and reloc['symbol']==name and imported['version']=='OPENSSL_3.0.0'
 assert not any(r['offset']<start+size and start<r['offset']+8 for r in elf.relocations for start,size in [(entry,len(code)),(pv,16)])
 links.append(dict(symbol=name,call_elf_vaddr=call['elf_vaddr'],call_loaded_address=BIAS+call['elf_vaddr'],call_displacement_signed=disp,call_displacement_u32=disp&0xffffffff,continuation_elf_vaddr=cont,continuation_loaded_address=BIAS+cont,plt_elf_vaddr=pv,plt_loaded_address=BIAS+pv,plt_file_offset=po,plt_bytes_hex=plt.hex(),plt_prefix_hex=plt[:6].hex(),plt_prefix_size=6,plt_prefix_sha256=sha(plt[:6]),plt_displacement_signed=pd,got_elf_vaddr=gv,got_loaded_address=BIAS+gv,got_file_offset=elf.extract(gv,8)[0],got_pointer_bytes=8,relocation=reloc,symbol_version=imported['version'],required_postinit_target=target,target_resolution='EXPLICIT_FIXED_POSTINITIALIZATION_LOADER_ASSUMPTION'))
assert any(d['tag']==30 and d['value']&8 for d in elf.dynamic)
assert all(r['type'] in (6,7,8) for r in elf.relocations)
cross={}
for section in ['.text','.plt']:
 g=(BUILT/'gnu-v1'/('gnu-'+section[1:]+'.bin')).read_bytes();py=elf.bytes(elf.byname[section]);assert g==py
 cross[section]=dict(status='PASS',length=len(g),gnu_sha256=sha(g),python_sha256=sha(py))
loads=[];immutable=[];initialized=[];pages={}
for p in elf.ph:
 if p['type']!=1:continue
 assert p['file_size']<=p['memory_size'] and p['file_offset']+p['file_size']<=len(elf.data)
 lo=BIAS+p['vaddr'];hi=lo+p['memory_size'];pl=lo//4096*4096;ph=(hi+4095)//4096*4096
 for page in range(pl,ph,4096):pages[page]=pages.get(page,0)|p['flags']
 (initialized if p['flags']&2 else immutable).append([lo,hi if p['flags']&2 else lo+p['file_size']])
 loads.append(dict(**p,loaded_file_interval=[lo,lo+p['file_size']],loaded_memory_interval=[lo,hi],mapped_page_interval=[pl,ph],initial_zero_fill_interval=[lo+p['file_size'],hi],source_segment_sha256=sha(elf.data[p['file_offset']:p['file_offset']+p['file_size']])))
relro,=[p for p in elf.ph if p['type']==0x6474e552]
rl=(BIAS+relro['vaddr'])//4096*4096;rh=(BIAS+relro['vaddr']+relro['memory_size'])//4096*4096
for page in range(rl,rh,4096):pages[page]&=~2
page_list=[dict(interval=[p,p+4096],read=bool(f&4),write=bool(f&2),execute=bool(f&1)) for p,f in sorted(pages.items())]
(HERE/'caller.bin').write_bytes(code);(HERE/'caller.hex').write_text(code.hex()+'\n')
for link in links:
 stem='crypto-plt-prefix' if link['symbol']=='CRYPTO_memcmp' else 'cleanse-plt-prefix'
 (HERE/(stem+'.bin')).write_bytes(bytes.fromhex(link['plt_prefix_hex']));(HERE/(stem+'.hex')).write_text(link['plt_prefix_hex']+'\n')
result=dict(schema='c3-final-linked-acquisition-v1',status='PASS_TRUSTED_EXACT_ARTIFACT_ACQUISITION_NOT_PROOF',experiment='BP-20261005-HELD-OUT-TRANSFER-V1',artifact='c3/artifact/compiled-v1/c3.so',artifact_sha256=elf.sha256,artifact_size=len(elf.data),elf_build_id=elf.build_id,source='c3/artifact/c3.S',source_sha256=sha((HERE/'c3.S').read_bytes()),source_kind='assembler-authored; GCC assembled and linked',build='c3/artifact/build-v1.sh',build_script_sha256=sha((HERE/'build-v1.sh').read_bytes()),build_image='sha256:444f775e6378c2e5523f29ceb8bbb184442277ed1114e6d37d873a7f127dfc26',parser_sha256=PARSER_SHA,load_bias=BIAS,permission_granule=4096,symbols=elf.symbols,sections=elf.sections,relocations=elf.relocations,program_headers=elf.ph,dynamic=elf.dynamic,needed=[d['string'] for d in elf.dynamic if d['tag']==1],caller=dict(symbol=symbol['name'],elf_vaddr=entry,file_offset=offset,loaded_address=BIAS+entry,size=len(code),bytes_hex=code.hex(),bytes_sha256=sha(code),instructions=rows,caller_instruction_count=len(rows),padding=[],prefix_step_count=10,initial_equal_caller_steps=31,initial_unequal_caller_steps=28,plt_transfer_steps=3,total_step_expression='(if initial_equal then34 else31)+2*bp_assurance_call_steps n+cleanse_functional_steps p n',downward_stack_envelope_bytes=48,scratch_interval_offsets=[-48,0],saved_register_slots=[dict(register='R13',offset=-8,size=8),dict(register='R12',offset=-16,size=8),dict(register='RBP',offset=-24,size=8),dict(register='RBX',offset=-32,size=8)],alignment_interval_offsets=[-40,-32],nested_call_slot=dict(offset=-48,size=8),profile_status='EXACT_BYTE_AND_DISASSEMBLY_INSPECTION_NOT_SEMANTICS_PROOF'),linkage=links,image=dict(segments=loads,immutable_file_backed_intervals=immutable,initialized_rw_intervals=initialized,page_permissions=page_list,mapped_page_interval=[min(pages),max(pages)+4096],relro_loaded_interval=[BIAS+relro['vaddr'],BIAS+relro['vaddr']+relro['memory_size']],relro_readonly_page_interval=[rl,rh],reference_image='Immutable PT_LOAD file bytes; explicit postinitialization RW memory including GOT and zero-fill; explicit mapped-page padding.'),gnu_python_section_crosscheck=cross,code_relocation_overlap=False,formal_parser_loader_isa_caller_proof=False,human_review='PENDING')
out=HERE/'inventory-v1.json';assert not out.exists();out.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['artifact_sha256','caller','linkage','image']},indent=2))
