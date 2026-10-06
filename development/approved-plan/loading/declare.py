#!/usr/bin/env python3
"""Declare the conditional post-initialization image; never execute a loader.

Trusted ELF inspection and exact code binding are explicit here. This program
cannot prove image existence, loader correctness, or a routine property.
"""
import hashlib,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
sys.path.insert(0,str(ROOT/'scripts'))
from inventory import ELF

def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 path=ROOT/'artifacts/baseline/libcrypto.so.3'
 if digest(path)!='76dd3d93e5ee48950a92a58d59b94de8143847f91a80d9682c938767b991577d':
  raise ValueError('Frozen artifact mismatch')
 elf=ELF(path);bias=0x10000000;P=4096
 segs=[]
 for s in elf.ph:
  if s['type']!=1:continue
  lo=(s['vaddr']//P)*P; hi=((s['vaddr']+s['memory_size']+P-1)//P)*P
  segs.append({'elf':s,'loaded_file_interval':[bias+s['vaddr'],bias+s['vaddr']+s['file_size']], 'source_file_interval':[s['file_offset'],s['file_offset']+s['file_size']], 'initial_zero_fill_interval':[bias+s['vaddr']+s['file_size'],bias+s['vaddr']+s['memory_size']], 'mapped_page_interval':[bias+lo,bias+hi], 'padding':'Bytes outside the mathematical PT_LOAD interval but inside its pages are ordinary stable public image bytes, explicitly unspecified. They are not target dependencies.'})
 relro=next(s for s in elf.ph if s['type']==0x6474e552)
 rrlo=bias+(relro['vaddr']//P)*P;rrhi=bias+((relro['vaddr']+relro['memory_size'])//P)*P
 target=next(x for x in json.loads((ROOT/'inventory/targets.json').read_text())['regions'] if x['entry_point']=='CRYPTO_memcmp')
 off,code=elf.extract(target['elf_vaddr'],target['size'])
 if off!=target['file_offset'] or code.hex()!=target['bytes_hex']:
  raise ValueError('Target code extraction mismatch')
 overlaps=[x for x in elf.relocations if x['offset']<target['elf_vaddr']+95 and target['elf_vaddr']<x['offset']+8]
 if overlaps:raise ValueError('Relocation overlaps code')
 data={'id':'BP-E2-CRYPTO-DECLARED-POSTIMAGE-V1','experiment_id':'BP-20260930-E2-CANDIDATE','artifact':str(path.relative_to(ROOT)),'artifact_sha256':digest(path),'elf_build_id':elf.build_id,'load_bias':bias,'permission_granule':P,'image_variable':'image : int64 -> byte','segments':segs,'relro_readonly_page_interval':[rrlo,rrhi],'postinit_writable_page_intervals':[[rrhi,max(s['mapped_page_interval'][1] for s in segs)]], 'entry_pc':bias+target['elf_vaddr'],'target_region':target,'target_relocation_overlaps':overlaps,'relocations':{'inventory':'inventory/relocations/libcrypto.so.3.json','sha256':digest(ROOT/'inventory/relocations/libcrypto.so.3.json'),'count':len(elf.relocations),'types':sorted(set(r['type'] for r in elf.relocations)),'loader_execution':'ASSUMED; no checked relocation algorithm','reached_by_CRYPTO_memcmp':[]},'postinit_image_assumptions':[
 'One consistent mathematical image map supplies every declared PT_LOAD page. The map agrees with frozen final-file bytes in file-backed immutable locations; no text relocations or interposition modify the target code.',
 'Ordinary loader relocation and initialization effects in writable data are explicit environmental poststate. Their resulting byte values remain arbitrary public image state for this routine, which has no global-data read or call.',
 'Initial BSS is zero-filled by the loading recipe; subsequent writable global state may change during initialization. No correctness behavior of a target routine is assumed.',
 'PT_GNU_RELRO pages become read-only after initialization. Mapped page permissions remain stable and are enforced by the unverified environment.',
 'The selected processor profile has CET disabled, 48-bit canonical addresses and AC clear; sequential execution has no concurrent changes to code, inputs, return slot, permissions or relevant processor state.'
 ],'binding_policy':{'code_predicate':'lw_reference_code image','formal_witness_extension':'lw_memory overlays only stack/input pages disjoint from declared library pages and must preserve image there','full_image_formalization':'NOT_YET_CHECKED','parser_formally_verified':False,'independent_extraction':'Required fresh GNU objcopy cross-check via scripts/check.py:binding; separate trust boundary, not a formal parser proof','loader_verified':False,'physical_permissions_verified':False},'status':'DECLARATION_ONLY_NOT_A_PROOF','human_review':'PENDING','input_hashes':{'scripts/inventory.py':digest(ROOT/'scripts/inventory.py'),'scripts/check.py':digest(ROOT/'scripts/check.py'),'inventory/artifacts.json':digest(ROOT/'inventory/artifacts.json'),'inventory/loading.json':digest(ROOT/'inventory/loading.json'),'declare.py':digest(Path(__file__))}}
 out=Path(__file__).with_name('declared-postimage-v1.json')
 if out.exists():raise ValueError('Explicit image declaration already exists; create a new version')
 out.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n');print(out)
if __name__=='__main__':main()
