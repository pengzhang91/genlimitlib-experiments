#!/usr/bin/env python3
"""Reproduce Section 5.2 from saved calls and the public presentation of inputs.

Usage: python3 scripts/reproduce_appendix_c.py
Requires Python 3 and no external packages, GPU, model calls, or network.
By default inputs are under experiments/ and sources/, and generated outputs
under results/, relative to this script's parent directory. Original files are
never edited. --project-root can select another copy of the organized bundle.
The extraction grammar intentionally matches E24/scripts/build_bank.py. A key-derived
signature is called exclusive only if it occurs in E12Keys and nowhere in either
original Lean source tree under that extraction grammar. This is textual provenance,
not an assertion that an equivalent mathematical proposition was absent elsewhere.
"""
import argparse
import collections
import gzip
import hashlib
import json
from pathlib import Path
import re
import statistics

from public_inputs import PublicInputs, BANK as PUBLIC_BANK

PUBLIC_INPUTS = None

MOD = {
    'P01': ('snap', 'Paper01_LanguageGeneration'),
    'P02': ('snap', 'Paper02_LearningTheory'),
    'P03': ('pub', 'Paper03_HallucinationAndModeCollapse'),
    'P04': ('snap', 'Paper04_ExploringFacetsOfLanguageGeneration'),
    'P05': ('pub', 'Paper05_HallucinationsBreadthAndStability'),
    'P06': ('snap', 'Paper06_NoisyExamples'),
    'P08': ('snap', 'Paper08_HallucinationDetection'),
    'P09': ('snap', 'Paper09_RepresentativeLanguageGeneration'),
    'P10': ('snap', 'Paper10_UnionClosednessOfLanguageGeneration'),
    'P12': ('snap', 'Paper12_NoiseLossAndFeedback'),
    'P17': ('snap', 'Paper17_InfiniteContamination'),
    'P19': ('snap', 'Paper19_EffectOfNoise'),
    'P23': ('snap', 'Paper23_BanachDensityTopologyAndGeometry'),
    'P28': ('snap', 'Paper28_ContrastiveGeneration'),
    'P31': ('pub', 'Paper31_BoundedMemory'),
    'P39': ('pub', 'Paper39_DenseGeneration'),
}
ARMS = {
    1: ['CLOSED', 'PAPER', 'PAPER_LEAN_OLD', 'PAPER_LEAN_NEW', 'PAPER_SHAM'],
    2: ['CLOSED', 'PAPERS', 'PAPERS_MAP', 'PAPERS_SHAMMAP'],
}
DECL = re.compile(r"^(?:noncomputable\s+)?(theorem|lemma|def|abbrev)\s+([A-Za-z_][\w']*)", re.M)
TERM = re.compile(r':=|\bby\b|\n\n')
BUNDLE = Path(__file__).resolve().parent.parent
# Translate archived project paths to the organized, self-contained bundle.
# Historical ledgers retain their original paths; generated hashes use the new
# bundle-relative names. This translation changes locations, never input bytes.
LAYOUT = {
    'outputs/E24_final_2026-09-19': 'experiments/01_final_evaluation',
    'outputs/E22_scale_2026-09-17': 'experiments/02_question_development/01_initial_batches',
    'outputs/E23_revised_2026-09-18': 'experiments/02_question_development/02_revised_and_audited',
    'outputs/E01S_paper_understanding_2026-09-13/inputs/source': 'sources/01_initial_lean_snapshot',
    'public-repo/GenLimitLean': 'sources/02_expanded_lean_library',
    'outputs/E12_round2_2026-09-16/corpus': 'sources/03_study_keys',
}


def bundle_relative_path(historical_path):
    for old, new in LAYOUT.items():
        if historical_path == old or historical_path.startswith(old + '/'):
            return new + historical_path[len(old):]
    raise ValueError('No bundle location for archived path: ' + historical_path)


def input_path(root, historical_path):
    return root / bundle_relative_path(historical_path)


def read_bytes(path):
    """Read a release input, transparently accepting deterministic gzip storage."""
    if PUBLIC_INPUTS is not None:
        restored = PUBLIC_INPUTS.read_override(path)
        if restored is not None:
            return restored
    if path.exists():
        return path.read_bytes()
    compressed = path.with_name(path.name + '.gz')
    if not compressed.exists():
        raise FileNotFoundError(path)
    with gzip.open(compressed, mode='rb') as handle:
        return handle.read()


def read_text(path):
    return read_bytes(path).decode('utf8')


def jsonl(path):
    # read_text also supplies exact restored input bytes in the optional full audit.
    for line in read_text(path).splitlines():
        yield json.loads(line)


def strip_comments(src):
    out, pos, depth = [], 0, 0
    while pos < len(src):
        if src.startswith('/-', pos):
            depth += 1
            pos += 2
        elif src.startswith('-/', pos) and depth:
            depth -= 1
            pos += 2
        elif depth:
            pos += 1
        elif src.startswith('--', pos):
            end = src.find('\n', pos)
            pos = len(src) if end < 0 else end
        else:
            out.append(src[pos])
            pos += 1
    return ''.join(out)


def cluster(item):
    label = (item.get('label') or '').strip()
    return '+'.join(item['papers']) + '|' + label if label else item['id']


def validate_raw_records(base, bank, retained, map_directory):
    """Check the complete frozen schedule and independently rerun the screen."""
    checks, recomputed_retained = {}, []
    map_blocks = {}
    for test in (1, 2):
        for stage, rotations in (('screen', (0, 1)), ('confirm', (2, 3, 4))):
            records = {}
            for kind, relative in (
                    ('prompts', f'prompts/t{test}_{stage}.jsonl'),
                    ('keys', f'inputs/t{test}_{stage}_key.jsonl'),
                    ('responses', f'runs/t{test}_{stage}_raw.jsonl')):
                rows = list(jsonl(base / relative))
                records[kind] = {r['request_id']: r for r in rows}
                if len(records[kind]) != len(rows):
                    raise ValueError('Duplicate request ID in ' + relative)
            ids = set(records['prompts'])
            if ids != set(records['keys']) or ids != set(records['responses']):
                raise ValueError(f'Prompt/key/response ID mismatch: t{test}_{stage}')
            items = {i for i, x in bank.items() if x['test'] == test
                     and (stage == 'screen' or i in retained)}
            arms = ['CLOSED'] if stage == 'screen' else ARMS[test]
            expected = {f'T{test}_{i}_{arm}_r{k}' for i in items
                        for arm in arms for k in rotations}
            if ids != expected:
                raise ValueError(f'Incomplete or extra request schedule: t{test}_{stage}')
            screen = collections.defaultdict(list)
            for rid, prompt in records['prompts'].items():
                item = bank[prompt['item_id']]
                k, arm = prompt['rot'], prompt['arm']
                if (prompt['test'] != test or k not in rotations or arm not in arms
                        or rid != f'T{test}_{item["id"]}_{arm}_r{k}'):
                    raise ValueError('Prompt metadata mismatch: ' + rid)
                shift = (int(hashlib.sha256(item['id'].encode()).hexdigest()[:8], 16) + k) % 5
                if records['keys'][rid]['gold'] != 'ABCDE'[shift]:
                    raise ValueError('Incorrect answer rotation: ' + rid)
                opts = [item['correct']] + item['distractors']
                permutation = [None] * 5
                permutation[shift] = 0
                rest = [1, 2, 3, 4] if k % 2 == 0 else [4, 3, 2, 1]
                for j, slot in enumerate(s for s in range(5) if s != shift):
                    permutation[slot] = rest[j]
                options = '\n'.join(f'{"ABCDE"[j]}. {opts[p]}' for j, p in enumerate(permutation))
                question = 'Question:\n' + item['stem'] + '\n\n' + options
                system, user = (m['content'] for m in prompt['messages'])
                if not user.endswith(question):
                    raise ValueError('Frozen question/options mismatch: ' + rid)
                digest = hashlib.sha256((system + '\x00' + user).encode()).hexdigest()
                if digest != prompt['prompt_sha256'] or len(system) + len(user) != prompt['chars']:
                    raise ValueError('Prompt hash/length mismatch: ' + rid)
                field = {'PAPER_LEAN_OLD': 'lean_old', 'PAPER_LEAN_NEW': 'lean_new',
                         'PAPER_SHAM': 'lean_sham'}.get(arm)
                if arm == 'CLOSED':
                    expected_user = question
                elif arm in ('PAPER', 'PAPERS'):
                    expected_user = (('Reference material:\n' + item['paper_text'] + '\n\n')
                                     if item['paper_text'] else '') + question
                elif field:
                    expected_user = ('Reference material:\n' + item['paper_text']
                                     + '\n\nSupplementary reference material:\n' + item[field]
                                     + '\n\n' + question)
                else:
                    prefix = ('Reference material:\n' + item['paper_text']
                              + '\n\nSupplementary reference material:\n')
                    if not user.startswith(prefix):
                        raise ValueError('Map prompt paper text mismatch: ' + rid)
                    block = user[len(prefix):-(len(question) + 2)]
                    if map_blocks.setdefault(arm, block) != block:
                        raise ValueError('Inconsistent frozen map material: ' + rid)
                    expected_user = prefix + block + '\n\n' + question
                if user != expected_user:
                    raise ValueError('Released prompt evidence mismatch: ' + rid)
                response = records['responses'][rid]
                if response['status'] != 'completed':
                    raise ValueError('Non-completed response: ' + rid)
                if stage == 'screen':
                    screen[item['id']].append(float(response['argmax'] == records['keys'][rid]['gold']))
            if stage == 'screen':
                recomputed_retained.extend(i for i, scores in screen.items()
                                          if statistics.mean(scores) <= .5)
            checks[f't{test}_{stage}'] = {
                'items': len(items), 'requests': len(ids), 'arms': arms,
                'rotations': list(rotations), 'unique_ids_and_complete_schedule': True,
                'prompt_hashes_and_bank_content_match': True,
                'answer_keys_and_option_rotations_match': True,
            }
    if set(recomputed_retained) != retained:
        raise ValueError('Recomputed closed-book screen does not match frozen screen.json')
    checks['screen_recomputed_from_raw'] = True
    checks['screen_retained_counts'] = dict(
        collections.Counter(str(bank[i]['test']) for i in sorted(retained)))
    checks['map_character_counts'] = {arm: len(block) for arm, block in map_blocks.items()}
    for arm, filename in (('PAPERS_MAP', 'MAP5.txt'), ('PAPERS_SHAMMAP', 'SHAMMAP5.txt')):
        path = map_directory / filename
        if map_blocks[arm] != path.read_text(encoding='utf8'):
            raise ValueError('Frozen supplementary material does not match ' + filename)
    checks['frozen_maps_match_copied_map_files'] = True
    return checks


def verify_expected(result, expected_path, analysis_path):
    """Compare source bytes and point estimates against the historical recount."""
    expected = json.loads(read_text(expected_path))

    def relative_hashes(mapping):
        normalized = {}
        for path, digest in mapping.items():
            match = re.search(r'(?:^|/)(outputs/.*|public-repo/.*)$', path)
            if not match:
                raise ValueError('Unrecognized archived source path: ' + path)
            normalized[bundle_relative_path(match.group(1))] = digest
        return normalized

    for field in ('source_sha256', 'archive_sha256'):
        archived_hashes = relative_hashes(expected[field])
        if field == 'archive_sha256':
            record = PUBLIC_INPUTS.manifest['files'][PUBLIC_BANK]
            if archived_hashes[PUBLIC_BANK] != record['original_sha256']:
                raise ValueError('Public manifest does not refer to the archived original bank')
            if not PUBLIC_INPUTS.restored:
                # Only this explicitly declared derivative hash is substituted.
                # Other historical source and input hashes remain exact checks.
                archived_hashes[PUBLIC_BANK] = record['public_sha256']
        if result[field] != archived_hashes:
            mismatched = sorted(p for p in set(result[field]) | set(archived_hashes)
                                if result[field].get(p) != archived_hashes.get(p))
            raise ValueError('Historical input/source hash mismatch: ' + ', '.join(mismatched[:8]))

    def compare(left, right, path):
        if isinstance(right, dict):
            for key, value in right.items():
                if key != 'ci95':  # Historical intervals are outside this release's scope.
                    compare(left[key], value, path + '/' + key)
        elif isinstance(right, list):
            if len(left) != len(right):
                raise ValueError('Historical list length mismatch at ' + path)
            for index, (a, b) in enumerate(zip(left, right)):
                compare(a, b, path + '/' + str(index))
        elif isinstance(right, float):
            if abs(left - right) > 1e-12:
                raise ValueError('Historical numerical mismatch at ' + path)
        elif left != right:
            raise ValueError('Historical value mismatch at ' + path)

    fields = ('bank_counts', 'test2_screened_categories', 'provenance_counts',
              'exclusive_study_key_signatures', 'prompt_checks', 'call_counts',
              'incomplete_letter_scores', 'provenance')
    for field in fields:
        compare(result[field], expected[field], field)
    for name, report in expected['reports'].items():
        compare(result['reports'][name], report, 'reports/' + name)
    # The original recount omitted this contrast; independently check its
    # point estimate against the frozen original analysis.
    original_analysis = json.loads(analysis_path.read_text())
    old_sham = result['reports']['test1_screened']['contrasts']['PAPER_LEAN_OLD - PAPER_SHAM']
    archived = original_analysis['test1_screened']['contrasts']['PAPER_LEAN_OLD - PAPER_SHAM']
    compare(old_sham['estimate'], archived[0], 'point_estimates/OLD-SHAM')
    result['validation']['historical_source_files_verified'] = len(result['source_sha256'])
    result['validation']['historical_input_hashes_match'] = PUBLIC_INPUTS.restored
    result['validation']['unchanged_historical_input_hashes_match'] = True
    result['validation']['historical_point_estimates_match'] = True
    result['validation']['old_minus_sham_point_estimate_matches_archived_analysis'] = True


def write_results(result, output_dir):
    reports = result['reports']
    labels = {
        'CLOSED': 'Question only', 'PAPER': 'Paper excerpts',
        'PAPER_SHAM': 'Paper + unrelated Lean',
        'PAPER_LEAN_OLD': 'Paper + Lean in file order',
        'PAPER_LEAN_NEW': 'Paper + relevant Lean',
        'PAPERS': 'No map', 'PAPERS_MAP': 'Relevant map',
        'PAPERS_SHAMMAP': 'Sham map',
    }
    displayed_arms = {
        1: ['CLOSED', 'PAPER', 'PAPER_SHAM', 'PAPER_LEAN_OLD', 'PAPER_LEAN_NEW'],
        2: ['PAPERS', 'PAPERS_MAP', 'PAPERS_SHAMMAP'],
    }
    accuracies = []
    for test in (1, 2):
        row = reports[f'test{test}_screened']
        for arm in displayed_arms[test]:
            accuracies.append({
                'test': test, 'arm': arm, 'information': labels[arm],
                'questions': row['n_items'], 'groups': row['n_clusters'],
                'accuracy_pct': row['cluster_means'][arm] * 100,
            })
    original = reports['test1_screened']
    filtered = reports['test1_exclude_outside_source_module_core']
    exclusion = {
        'criterion': 'At least one relevant-Lean declaration signature outside the source module and Core.',
        'excluded_questions': original['n_items'] - filtered['n_items'],
        'remaining_questions': filtered['n_items'],
        'remaining_groups': filtered['n_clusters'],
        'relevant_lean_accuracy_pct': filtered['cluster_means']['PAPER_LEAN_NEW'] * 100,
        'question_ids': result['provenance_counts']['outside_source_module_core']['screened_ids'],
    }
    categories = []
    for label, key in (('Two-paper', 'multiple_source_candidate'),
                       ('One-paper', 'single_paper'), ('Stem-only', 'stem_only'),
                       ('Repository', 'repository_only')):
        row = reports['test2_' + key]
        categories.append({
            'category': label, 'questions': row['n_items'], 'groups': row['n_clusters'],
            'no_map_pct': row['cluster_means']['PAPERS'] * 100,
            'relevant_map_pct': row['cluster_means']['PAPERS_MAP'] * 100,
            'sham_map_pct': row['cluster_means']['PAPERS_SHAMMAP'] * 100,
            'map_minus_sham_pp': row['contrasts']['PAPERS_MAP - PAPERS_SHAMMAP']['estimate'] * 100,
        })
    summary = {
        'scope': 'Section 5.2 and the shortened Appendix C.',
        'units': 'Accuracy in percent; differences in percentage points.',
        'method': result['method'], 'validation': result['validation'],
        'main_accuracies': accuracies,
        'exclusion_check': exclusion,
        'map_categories': categories,
    }
    (output_dir / 'section5_2_results.json').write_text(json.dumps(summary, indent=2) + '\n')
    lines = [
        '# Section 5.2: reproduced results', '',
        'Generated from frozen response records by `python3 scripts/reproduce_appendix_c.py`.', '',
        'For each question, correctness is averaged over three evaluation rotations. '
        'Questions with the same recorded paper identifiers and source label form a group; '
        'a question without a source label forms its own group. Question scores are averaged '
        'within each group, then groups receive equal weight. The same questions, rotations, '
        'and groups are used in every condition within a study.', '',
        '## Main results', '',
        '| Study | Information supplied | Questions | Accuracy (%) |',
        '| --- | --- | ---: | ---: |',
    ]
    for row in accuracies:
        study = 'Individual papers' if row['test'] == 1 else 'Five-paper collection'
        lines.append(f"| {study} | {row['information']} | {row['questions']} | {row['accuracy_pct']:.2f} |")
    lines += [
        '', '## Checks supporting the main-text qualifications', '',
        f"Excluding {exclusion['excluded_questions']} questions with relevant-Lean signatures "
        f"outside the source module and Core leaves {exclusion['remaining_questions']} questions "
        f"and relevant-Lean accuracy of **{exclusion['relevant_lean_accuracy_pct']:.2f}%**. "
        'This is an exact textual-signature check; it does not establish the absence of '
        'mathematically equivalent statements elsewhere.', '',
        'The category point estimates below support the main-text observation that map gains '
        'occur mainly outside questions requiring two papers.', '',
        '| Category | Questions | No map (%) | Relevant map (%) | Sham map (%) | Map minus sham (pp) |',
        '| --- | ---: | ---: | ---: | ---: | ---: |',
    ]
    for row in categories:
        lines.append(f"| {row['category']} | {row['questions']} | {row['no_map_pct']:.2f} | {row['relevant_map_pct']:.2f} | {row['sham_map_pct']:.2f} | {row['map_minus_sham_pp']:.2f} |")
    lines += [
        '', '## Reproduction checks', '',
        '- Prompt, answer-key, and response IDs and complete condition/rotation schedules verified.',
        '- Released questions, options, Lean/map blocks, and excerpt locators checked for internal consistency.',
        ('- Complete review-snapshot bank and prompt bytes restored and verified against original hashes.'
         if PUBLIC_INPUTS.restored else
         '- Omitted original excerpt text is not verified in this public-only run; use --private-excerpts for full input verification.'),
        '- Screening independently recomputed from raw responses and matched to the retained set.',
        '- Unchanged input/source hashes and all reported point estimates checked against historical records.',
        '- Public derivative input hashes checked against PUBLIC_RELEASE.json; original hashes retained separately.',
        '- Saved responses were not regenerated after review-time redactions or public excerpt omission.', '',
        f"Bank: {result['bank_counts']['1']} single-paper and {result['bank_counts']['2']} map-study questions.",
        f"Source files verified: {result['validation']['historical_source_files_verified']}.",
        f"Responses with fewer than five recorded option scores: {len(result['incomplete_letter_scores'])}; "
        'these records are preserved and scored using the archived argmax.', '',
        'The historical reference inputs retain the original analysis fields. This release '
        'reproduces point estimates and does not calculate or report confidence intervals.', '',
    ]
    (output_dir / 'section5_2_results.md').write_text('\n'.join(lines))


def main():
    global PUBLIC_INPUTS
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--project-root', type=Path,
                        default=BUNDLE,
                        help='Root of the organized bundle containing experiments/ and sources/.')
    parser.add_argument('--output', type=Path, default=BUNDLE / 'results/recount.json')
    parser.add_argument('--expected', type=Path, default=BUNDLE / 'archive/recount_e24_20260920.json',
                        help='Archived recount used to verify data, source hashes and estimates.')
    parser.add_argument('--private-excerpts', type=Path,
                        help='Local JSON mapping original excerpt SHA-256 to complete text; never uploaded or written by this script.')
    args = parser.parse_args()
    root = args.project_root.resolve()
    PUBLIC_INPUTS = PublicInputs(root, args.private_excerpts)
    base = input_path(root, 'outputs/E24_final_2026-09-19')
    roots = {
        'snap': input_path(root, 'outputs/E01S_paper_understanding_2026-09-13/inputs/source/lean_sources/GenLimit'),
        'pub': input_path(root, 'public-repo/GenLimitLean/GenLimit'),
    }
    key_path = input_path(root, 'outputs/E12_round2_2026-09-16/corpus/E12Keys.lean')
    map_directory = input_path(root, 'outputs/E22_scale_2026-09-17/inputs')
    bank_rows = json.loads(read_text(base / 'inputs/bank24.json'))
    bank = {x['id']: x for x in bank_rows}
    if len(bank) != len(bank_rows):
        raise ValueError('Duplicate item IDs in bank24.json')
    retained = set(json.loads((base / 'analysis/screen.json').read_text())['retained'])
    validation = validate_raw_records(base, bank, retained, map_directory)
    validation.update(PUBLIC_INPUTS.validation())
    print('Verified released prompt consistency, schedules, rotations, and the raw-data screen.', flush=True)
    print('Full original input hashes verified: ' + str(PUBLIC_INPUTS.restored), flush=True)
    hashes, cache = {}, {}

    def declarations(path):
        if path not in cache:
            raw = path.read_bytes()
            hashes[path.relative_to(root).as_posix()] = hashlib.sha256(raw).hexdigest()
            src = strip_comments(raw.decode('utf8', errors='ignore'))
            out = []
            for match in DECL.finditer(src):
                kind, name = match.group(1), match.group(2)
                suffix = src[match.end():match.end() + 900]
                end = TERM.search(suffix)
                sig = re.sub(r'\s+', ' ',
                             (name + (suffix[:end.start()] if end else suffix)).strip())
                if 25 < len(sig) < 240:
                    out.append((kind + ' ' + sig, name))
            cache[path] = out
        return cache[path]

    def module(root_path, name):
        paths = sorted((root_path / name).rglob('*.lean')) if (root_path / name).exists() else []
        if (root_path / (name + '.lean')).exists():
            paths.append(root_path / (name + '.lean'))
        out, seen = [], set()
        for path in paths:
            for sig, leaf in declarations(path):
                if leaf not in seen:
                    seen.add(leaf)
                    out.append((sig, leaf))
        return out

    core = module(roots['snap'], 'Core')
    pools = {paper: module(roots[which], name) + core
             for paper, (which, name) in MOD.items()}
    print('Loaded source-module and Core candidate pools.', flush=True)
    original_origins = collections.defaultdict(list)
    for source_root in roots.values():
        for path in sorted(source_root.rglob('*.lean')):
            for sig, _ in declarations(path):
                original_origins[sig].append(path.relative_to(root).as_posix())
    key_sigs = {sig for sig, _ in declarations(key_path)}
    exclusive_key_sigs = key_sigs - set(original_origins)
    print('Loaded all original source signatures and E12Keys.', flush=True)

    provenance = {}
    for ident, item in bank.items():
        if item['test'] != 1:
            continue
        paper = item['papers'][0] if item['papers'][0] in pools else 'P02'
        allowed = {sig for sig, _ in pools[paper]}
        arms = {}
        for field in ('lean_old', 'lean_new', 'lean_sham'):
            sigs = [s for s in item[field].splitlines() if DECL.match(s)]
            arms[field] = {
                'study_key_signature_overlap': [s for s in sigs if s in key_sigs],
                'exclusive_study_key_signatures': [s for s in sigs if s in exclusive_key_sigs],
                'outside_source_module_and_core': [s for s in sigs if s not in allowed],
            }
        provenance[ident] = {'screened': ident in retained, 'papers': item['papers'],
                             'basis': item.get('basis'), 'arms': arms}

    outside = {i for i, x in provenance.items()
               if x['arms']['lean_new']['outside_source_module_and_core']}
    exclusive = {i for i, x in provenance.items()
                 if x['arms']['lean_new']['exclusive_study_key_signatures']}
    any_key = {i for i, x in provenance.items()
               if any(z['exclusive_study_key_signatures'] for z in x['arms'].values())}
    prefix = {i for i in provenance if (bank[i].get('basis') or '').startswith('E12.')}
    mention = {i for i in provenance if 'E12' in (bank[i].get('basis') or '')}

    prompt_checks = collections.Counter()
    for rec in jsonl(base / 'prompts/t1_confirm.jsonl'):
        field = {'PAPER_LEAN_OLD': 'lean_old', 'PAPER_LEAN_NEW': 'lean_new',
                 'PAPER_SHAM': 'lean_sham'}.get(rec['arm'])
        if field:
            expected = bank[rec['item_id']][field]
            token = '\n\nSupplementary reference material:\n' + expected + '\n\nQuestion:\n'
            if token not in rec['messages'][1]['content']:
                raise ValueError('Released prompt does not match bank: ' + rec['request_id'])
            prompt_checks[rec['arm']] += 1
    print('Verified all Test-1 supplementary blocks in released confirm prompts.', flush=True)

    data = {}
    call_counts, incomplete = {}, []
    for test in (1, 2):
        keys = {r['request_id']: r['gold'] for r in jsonl(base / f'inputs/t{test}_confirm_key.jsonl')}
        meta = {f'T{test}_{i}_{arm}_r{k}': (i, arm)
                for i, x in bank.items() if x['test'] == test and i in retained
                for arm in ARMS[test] for k in (2, 3, 4)}
        dd = collections.defaultdict(lambda: collections.defaultdict(list))
        for rec in jsonl(base / f'runs/t{test}_confirm_raw.jsonl'):
            ident, arm = meta[rec['request_id']]
            if rec['status'] != 'completed':
                raise ValueError('Non-completed response: ' + rec['request_id'])
            dd[ident][arm].append(float(rec['argmax'] == keys[rec['request_id']]))
        for ident in dd:
            if any(len(dd[ident][arm]) != 3 for arm in ARMS[test]):
                raise ValueError('Missing rotation for ' + ident)
        data[test] = dd
        for stage in ('screen', 'confirm'):
            path = base / f'runs/t{test}_{stage}_raw.jsonl'
            keys_stage = {r['request_id']: r['gold'] for r in jsonl(base / f'inputs/t{test}_{stage}_key.jsonl')}
            counts = collections.Counter()
            for rec in jsonl(path):
                counts[rec['status']] += 1
                if rec['n_letters_seen'] != 5:
                    incomplete.append({'request_id': rec['request_id'],
                                       'n_letters_seen': rec['n_letters_seen'],
                                       'argmax': rec['argmax'], 'gold': keys_stage[rec['request_id']],
                                       'letter_logprobs': rec['letter_logprobs']})
            call_counts[path.name] = dict(counts)

    def report(test, ids):
        ids = set(ids)
        # Preserve the recorded question order for comparison with the historical ledger.
        chosen = [i for i in data[test] if i in ids]
        dd = data[test]
        groups = collections.defaultdict(list)
        for ident in chosen:
            groups[cluster(bank[ident])].append(ident)
        means = {arm: statistics.mean(
            statistics.mean(statistics.mean(dd[i][arm]) for i in group)
            for group in groups.values()) for arm in ARMS[test]}
        item_means = {arm: statistics.mean(statistics.mean(dd[i][arm]) for i in chosen)
                      for arm in ARMS[test]}
        contrasts = [('PAPER_LEAN_NEW', 'PAPER_SHAM'),
                     ('PAPER_LEAN_OLD', 'PAPER_SHAM'),
                     ('PAPER_LEAN_NEW', 'PAPER_LEAN_OLD')] if test == 1 else [('PAPERS_MAP', 'PAPERS_SHAMMAP')]
        effects = {}
        for left, right in contrasts:
            values = [sum(statistics.mean(dd[i][left]) - statistics.mean(dd[i][right])
                          for i in group) / len(group) for group in groups.values()]
            effects[left + ' - ' + right] = {'estimate': sum(values) / len(values)}
        return {'n_items': len(chosen), 'n_clusters': len(groups),
                'cluster_means': means, 'item_means': item_means, 'contrasts': effects,
                'item_ids': chosen}

    reports = {'test1_screened': report(1, data[1])}
    for label, excluded in [('outside_source_module_core', outside),
                            ('exclusive_study_key_in_new', exclusive),
                            ('exclusive_study_key_in_any_arm', any_key),
                            ('E12_prefixed_basis', prefix), ('any_E12_basis_mention', mention)]:
        reports['test1_exclude_' + label] = report(1, set(data[1]) - excluded)
    manipulated = set()
    for ident in data[1]:
        item = bank[ident]
        basis = (item.get('basis') or '').strip()
        if not basis or ' ' in basis or len(basis) <= 6 or not re.fullmatch(r"[A-Za-z0-9_.']+", basis):
            continue
        leaf = re.escape(basis.split('.')[-1])
        if (re.search(r'^(theorem|lemma) ' + leaf + r'\b', item['lean_new'], re.M)
                and not re.search(r'\b' + leaf + r'\b', item['lean_old'])):
            manipulated.add(ident)
    reports['test1_theorem_manipulation'] = report(1, manipulated)
    reports['test1_theorem_manipulation_exclude_outside'] = report(1, manipulated - outside)
    reports['test2_screened'] = report(2, data[2])
    for flag in ('multiple_source_candidate', 'single_paper', 'stem_only', 'repository_only'):
        reports['test2_' + flag] = report(2, [i for i in data[2] if bank[i].get('t2_flag') == flag])

    result = {
        'method': {'estimand': 'Equal weight per group of recorded paper identifiers and source label (unlabeled questions stand alone); equal weight per question within group and per held-out rotation within question.',
                   'provenance_scope': 'Exact extracted declaration signatures; no claim about mathematical equivalence.',
                   'inputs_unchanged': False,
                   'anonymous_release_redactions':
                       'Historical identity/contact redactions preceded this public export; archived responses were not regenerated.',
                   'public_excerpt_omissions':
                       'Unresolved excerpts replaced by boundary locators in public files; original hashes kept separately.',
                   'input_validation_scope': validation['input_scope']},
        'bank_counts': dict(collections.Counter(str(x['test']) for x in bank.values())),
        'test2_screened_categories': dict(collections.Counter(bank[i].get('t2_flag') for i in data[2])),
        'provenance_counts': {label: {'bank': len(ids), 'screened': len(ids & retained),
                                     'theorem_manipulation': len(ids & manipulated),
                                     'screened_ids': sorted(ids & retained)}
                              for label, ids in [('outside_source_module_core', outside),
                                                 ('exclusive_study_key_in_new', exclusive),
                                                 ('exclusive_study_key_in_any_arm', any_key),
                                                 ('E12_prefixed_basis', prefix),
                                                 ('any_E12_basis_mention', mention)]},
        'exclusive_study_key_signatures': sorted(exclusive_key_sigs),
        'prompt_checks': dict(prompt_checks), 'call_counts': call_counts,
        'incomplete_letter_scores': incomplete, 'reports': reports,
        'provenance': provenance, 'source_sha256': hashes, 'validation': validation,
    }
    for name in ('inputs/bank24.json', 'analysis/results.json', 'analysis/screen.json'):
        path = base / name
        result.setdefault('archive_sha256', {})[path.relative_to(root).as_posix()] = hashlib.sha256(read_bytes(path)).hexdigest()
    verify_expected(result, args.expected, base / 'analysis/results.json')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    write_results(result, args.output.parent)
    print('Wrote recount.json, section5_2_results.json, and section5_2_results.md.', flush=True)


if __name__ == '__main__':
    main()
