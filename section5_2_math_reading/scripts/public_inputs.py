"""Validate public excerpt locators and optionally restore private input bytes.

This module never writes files. Private excerpts stay local and are not echoed.
"""
import gzip
import hashlib
import json
from pathlib import Path

BANK = 'experiments/01_final_evaluation/inputs/bank24.json'
ARCHIVE = 'archive/recount_e24_20260920.json'
PROMPTS = [f'experiments/01_final_evaluation/prompts/t{n}_confirm.jsonl' for n in (1, 2)]

def digest(data):
    return hashlib.sha256(data).hexdigest()

def encode(value, record):
    opts = {'ensure_ascii': record['codec']['ensure_ascii'],
            'separators': tuple(record['codec']['separators']),
            'indent': record['codec'].get('indent')}
    if record['format'] == 'jsonl':
        return ''.join(json.dumps(row, **opts) + '\n' for row in value).encode('utf8')
    return (json.dumps(value, **opts) + '\n').encode('utf8')

class PublicInputs:
    def __init__(self, root, private_excerpts=None):
        self.root = Path(root).resolve()
        self.manifest = json.loads((self.root / 'PUBLIC_RELEASE.json').read_text())
        self.restored = private_excerpts is not None
        self.overrides = {}
        manifest = self.manifest
        if manifest['schema_version'] != 1 or set(manifest['files']) != {BANK, ARCHIVE, *PROMPTS}:
            raise ValueError('Unsupported public release manifest')
        excerpts = manifest['excerpts']
        if len({e['public_text'] for e in excerpts.values()}) != len(excerpts):
            raise ValueError('Duplicate public excerpt locator')
        private = json.loads(Path(private_excerpts).read_text()) if self.restored else {}
        for h, item in excerpts.items():
            if item['sha256'] != h:
                raise ValueError('Excerpt registry hash/key mismatch')
            if self.restored:
                text = private.get(h)
                if (not isinstance(text, str) or digest(text.encode()) != h
                        or len(text) != item['original_chars']
                        or len(text.encode()) != item['original_utf8_bytes']
                        or not text.startswith(item['first_boundary'])
                        or not text.endswith(item['last_boundary'])):
                    raise ValueError('Missing or incorrect private excerpt: ' + h)
        payloads = {}
        for name, rec in manifest['files'].items():
            if rec['stored_path'] != (name if name == ARCHIVE else name + '.gz'):
                raise ValueError('Unexpected stored input path')
            stored = (self.root / rec['stored_path']).read_bytes()
            raw = stored if name == ARCHIVE else gzip.decompress(stored)
            if digest(raw) != rec['public_sha256']:
                raise ValueError('Public input hash mismatch: ' + name)
            payloads[name] = ([json.loads(line) for line in raw.splitlines()]
                              if rec['format'] == 'jsonl' else json.loads(raw))
        seen = set()
        for row in payloads[BANK]:
            h = manifest['bank_excerpts'].get(row['id'])
            if h is not None:
                if h not in excerpts or row['paper_text'] != excerpts[h]['public_text']:
                    raise ValueError('Bank excerpt locator mismatch: ' + row['id'])
                if row['id'] not in excerpts[h]['question_ids']:
                    raise ValueError('Excerpt/question association mismatch')
                seen.add(row['id'])
                if self.restored:
                    row['paper_text'] = private[h]
        if seen != set(manifest['bank_excerpts']):
            raise ValueError('Missing bank excerpt records')
        for name in PROMPTS:
            seen = set()
            for row in payloads[name]:
                rec = manifest['prompt_records'][name].get(row['request_id'])
                if rec is None:
                    continue
                h = rec['excerpt_sha256']
                if row['arm'] == 'CLOSED' or manifest['bank_excerpts'].get(row['item_id']) != h:
                    raise ValueError('Invalid public prompt mapping')
                prefix = 'Reference material:\n' + excerpts[h]['public_text']
                if not row['messages'][1]['content'].startswith(prefix):
                    raise ValueError('Public prompt locator mismatch: ' + row['request_id'])
                seen.add(row['request_id'])
                if self.restored:
                    suffix = row['messages'][1]['content'][len(prefix):]
                    row['messages'][1]['content'] = 'Reference material:\n' + private[h] + suffix
                    row['prompt_sha256'] = rec['original_prompt_sha256']
                    row['chars'] = rec['original_chars']
            if seen != set(manifest['prompt_records'][name]):
                raise ValueError('Missing public prompt records')
        by_id = {row['id']: row for row in payloads[BANK]}
        for ident, h in manifest['basis_excerpts'].items():
            bank_row = by_id[ident]
            archived_row = payloads[ARCHIVE]['provenance'].get(ident)
            for row in [bank_row, archived_row]:
                if row is None:
                    continue
                if row['basis'] != excerpts[h]['public_text']:
                    raise ValueError('Supporting quote locator mismatch: ' + ident)
                if self.restored:
                    row['basis'] = private[h]
        if self.restored:
            for name, value in payloads.items():
                raw = encode(value, manifest['files'][name])
                if digest(raw) != manifest['files'][name]['original_sha256']:
                    raise ValueError('Restored input differs from original snapshot: ' + name)
                self.overrides[(self.root / name).resolve()] = raw

    def read_override(self, path):
        return self.overrides.get(Path(path).resolve())

    def validation(self):
        return {
            'public_input_hashes_verified': True,
            'public_excerpt_registry_verified': True,
            'original_full_input_hashes_verified': self.restored,
            'full_prompt_audit_requires_private_excerpts': not self.restored,
            'public_excerpt_counts': self.manifest['counts'],
            'input_scope': ('restored review-snapshot bytes, after historical identity redactions'
                            if self.restored else 'public locator presentation; omitted text not verified'),
        }
