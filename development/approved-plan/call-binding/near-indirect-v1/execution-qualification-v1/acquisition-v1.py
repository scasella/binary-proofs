"""Trusted byte/PT_LOAD acquisition only; no caller implementation proof."""
import hashlib,json,re
from pathlib import Path

def acquire(root):
 from inventory import ELF
 inv=json.loads((root/'inventory/clients.json').read_text())
 elf=ELF(root/inv['path'])
 if elf.sha256!=inv['artifact_sha256']:raise RuntimeError('Caller artifact hash mismatch')
 rows=[]
 for region in inv['caller_regions']:
  off,data=elf.extract(region['elf_vaddr'],region['size'])
  if off!=region['file_offset'] or data.hex()!=region['bytes_hex'] or hashlib.sha256(data).hexdigest()!=region['bytes_sha256']:raise RuntimeError('Caller byte acquisition mismatch')
  rows.append(dict(region))
 prefixes=[]
 for row in inv['call_bindings']:
  off,data=elf.extract(row['plt_elf_vaddr'],6)
  if off!=row['plt_file_offset'] or data.hex()!=row['plt_bytes_hex'][:12]:raise RuntimeError('PLT byte acquisition mismatch')
  displacement=int.from_bytes(data[2:6],'little',signed=True)
  if row['plt_elf_vaddr']+6+displacement!=row['got_elf_vaddr']:raise RuntimeError('PLT/GOT displacement mismatch')
  prefixes.append({'symbol':row['symbol'],'prefix_hex':data.hex(),'file_offset':off,'plt_elf_vaddr':row['plt_elf_vaddr'],'got_elf_vaddr':row['got_elf_vaddr']})
 # Exact HOL code lists are checked independently against raw final file.
 lane=root/'development/approved-plan/call-binding/near-indirect-v1/execution-qualification-v1'
 for symbol,constant in [('secret_equal_and_clear','r1_secret_caller_mc'),('public_buffers_equal','r1_public_caller_mc')]:
  source=(lane/'abi-v6/code-v1.ml').read_text()
  code=re.search(r'let '+constant+r' = new_definition\s*`'+constant+r' = \[([^]]+)\]',source).group(1)
  values=bytes(int(v,0) for v in re.findall(r'word\s+(0x[0-9a-f]+|[0-9]+)',code))
  expected=next(r for r in rows if r['entry_point']==symbol)
  if values.hex()!=expected['bytes_hex']:raise RuntimeError('HOL caller byte-list mismatch')
 source=(root/'development/approved-plan/call-binding/near-indirect-v1/loaded-stub-v1/spec-v2.ml').read_text()
 for symbol,constant in [('CRYPTO_memcmp','r1_crypto_plt_prefix'),('OPENSSL_cleanse','r1_cleanse_plt_prefix'),('memcmp','r1_memcmp_plt_prefix')]:
  code=re.search(r'let '+constant+r' = new_definition\s*`'+constant+r' =\s*\[([^]]+)\]',source).group(1)
  values=bytes(int(v,0) for v in re.findall(r'word\s+(0x[0-9a-f]+|[0-9]+)',code))
  if values.hex()!=next(r for r in prefixes if r['symbol']==symbol)['prefix_hex']:raise RuntimeError('HOL PLT byte-list mismatch')
 return {'status':'PASS_TRUSTED_EXACT_CALLER_AND_PLT_BYTES','artifact_sha256':elf.sha256,'inventory_sha256':hashlib.sha256((root/'inventory/clients.json').read_bytes()).hexdigest(),'regions':rows,'plt_prefixes':prefixes,'formal_ELF_parser_proof':False,'human_review':'PENDING','caller_reachability_proof':False}
