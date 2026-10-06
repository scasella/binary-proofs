#!/usr/bin/env python3
"""Fresh trusted acquisition of the exact production cleanse entry bytes.

Reuses the complete ELF/PT_LOAD/RELRO external interpretation; the additional
97-byte claim is checked directly against the entire hashed file, its unique
RX segment, exact HOL literal and relocation inventory. No loader proof.
"""
from pathlib import Path
import hashlib,importlib.util,json,re,struct
ROOT=Path(__file__).resolve().parents[4]
def acquire():
 old=ROOT/'development/approved-plan/loaded-witness/full-binding/acquire-file-map-v2.py'
 spec=importlib.util.spec_from_file_location('clw_filemap',old)
 mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
 full=mod.acquire()
 raw=(ROOT/'artifacts/baseline/libcrypto.so.3').read_bytes()
 hdr=struct.unpack_from('<HHIQQQIHHHHHH',raw,16)
 phoff,phentsize,phnum=hdr[4],hdr[8],hdr[9]
 seg=[]
 for i in range(phnum):
  pt,perm,off,va,pa,fs,ms,align=struct.unpack_from('<IIQQQQQQ',raw,phoff+i*phentsize)
  if pt==1 and va<=0x2417d0 and 0x2417d0+97<=va+fs:seg.append((perm,off,va))
 if len(seg)!=1 or seg[0][0]!=5:raise ValueError('cleanse not uniquely file-backed RX')
 perm,off,va=seg[0];file_offset=off+0x2417d0-va
 if file_offset!=0x2417d0:raise ValueError('cleanse final-file offset mismatch')
 src=(ROOT/'proofs/qualification/openssl_bytes.ml').read_text()
 match=re.search(r'let openssl_cleanse_mc = new_definition\s*`([^`]+)`',src)
 if not match:raise ValueError('cleanse HOL definition absent')
 code=bytes(int(x,16) for x in re.findall(r'word (0x[0-9a-f]+)',match[1]))
 if len(code)!=97 or raw[file_offset:file_offset+97]!=code:raise ValueError('cleanse actual97 differs from literal')
 declaration=json.loads((ROOT/'development/approved-plan/loading/declared-postimage-v1.json').read_text())
 rr=json.loads((ROOT/declaration['relocations']['inventory']).read_text())
 records=rr if isinstance(rr,list) else rr.get('relocations',[])
 if any(r['offset']<0x2417d0+97 and 0x2417d0<r['offset']+8 for r in records):raise ValueError('relocation overlaps cleanse')
 cross=ROOT/'development/approved-plan/loaded-witness/full-binding/crosscheck-image-clauses-v1.py'
 xs=importlib.util.spec_from_file_location('clw_cross',cross)
 xm=importlib.util.module_from_spec(xs);xs.loader.exec_module(xm)
 # Crosscheck script is separately executed by replay; acquisition keeps the
 # entire PT_LOAD record and exact raw code correspondence together.
 return {'status':'PASS_TRUSTED_CLEANSE_FULL_IMAGE_ACQUISITION','whole_file_map':full,
  'code_file_offset':file_offset,'code_elf_vaddr':0x2417d0,'loaded_entry':0x102417d0,
  'code_bytes':97,'code_sha256':hashlib.sha256(code).hexdigest(),
  'clw_file_code_external_check':True,'unique_RX_segment':True,'relocation_overlap':False,
  'formal_parser_or_loader_proof':False,'human_review':'PENDING',
  'initial_RW_and_padding':'explicit post-initialization parameters; initial-only binding'}
if __name__=='__main__':print(json.dumps(acquire(),indent=2,sort_keys=True))
