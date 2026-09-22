import * as path from 'path';
import type {
  FileReaderPort,
  FileWriterPort,
  HashPort,
} from '../../domain/utils/io-port.contract.js';
import { CHUNK_PREFIX } from '../../domain/core/chunk.js';
import { DEFAULT_HASH_SLOT, hashChunkContent, hashSlotOf } from '../../utils/hash.js';

type RenameDeps = FileReaderPort & FileWriterPort & HashPort;

// The hash segment of a bundler's output name, whichever alphabet it was written in.
const HASH_SEGMENT = /-([A-Za-z0-9_]+)$/;

const SOURCE_EXTENSION = /\.(m|c)?js$/;
const SOURCE_MAP_COMMENT = /\/\/# sourceMappingURL=\S+\s*$/;

// `'./chunk-x.js'` as the bundler wrote it, or `'@nf-internal/chunk-x'` after the import rewrite.
const CHUNK_REFERENCE = new RegExp(`(['"])(?:\\.\\/([^'"/]+)|${CHUNK_PREFIX}\\/([^'"/]+))\\1`, 'g');

/**
 * The bundler names a chunk after the build graph it belongs to, so two applications can emit
 * different bytes under one name and identical bytes under two. Both break sharing by name: the
 * first hands one application the other's file, the second keeps one module as two. The hash
 * segment is therefore replaced by a hash of the bytes that will be served, dependencies first,
 * because renaming a chunk changes the text of everything that imports it.
 *
 * `chunks` and `referrers` are file names inside `dir`; only the former are renamed, the latter
 * have their references updated. Returns the renames as old name → new name.
 */
export function renameChunksByContentCore(
  io: RenameDeps,
  dir: string,
  chunks: string[],
  referrers: string[]
): Map<string, string> {
  const chunkSet = new Set(chunks);
  const byStem = new Map(chunks.map(file => [stemOf(file), file]));
  const renamed = new Map<string, string>();
  const visiting = new Set<string>();

  const referencedChunks = (text: string): string[] => {
    const found: string[] = [];
    for (const [, , relative, bare] of text.matchAll(CHUNK_REFERENCE)) {
      const file = relative !== undefined ? relative : byStem.get(bare!);
      if (file && chunkSet.has(file)) found.push(file);
    }
    return found;
  };

  const withRenames = (text: string): string =>
    text.replace(CHUNK_REFERENCE, (match, quote: string, relative?: string, bare?: string) => {
      const file = relative !== undefined ? relative : byStem.get(bare!);
      const target = file && renamed.get(file);
      if (!target) return match;
      return relative !== undefined
        ? `${quote}./${target}${quote}`
        : `${quote}${CHUNK_PREFIX}/${stemOf(target)}${quote}`;
    });

  const settle = (file: string): void => {
    if (renamed.has(file) || visiting.has(file)) return;
    visiting.add(file);
    const text = io.readText(path.join(dir, file));
    for (const dependency of referencedChunks(text)) settle(dependency);
    visiting.delete(file);

    const body = withRenames(text).replace(SOURCE_MAP_COMMENT, '');
    renamed.set(file, hashedName(io, file, body));
  };

  for (const chunk of chunks) settle(chunk);

  // Written only once every name is final: inside an import cycle the first chunk is hashed
  // before its partner is renamed, so its text is settled here rather than at hashing time.
  for (const file of chunks) {
    const target = renamed.get(file)!;
    const source = path.join(dir, file);
    const text = withRenames(io.readText(source)).split(`${file}.map`).join(`${target}.map`);
    io.writeText(path.join(dir, target), text);
    if (target === file) continue;
    io.remove(source);
    if (io.exists(`${source}.map`)) {
      io.copyFile(`${source}.map`, path.join(dir, `${target}.map`));
      io.remove(`${source}.map`);
    }
  }

  for (const file of referrers) {
    const filePath = path.join(dir, file);
    const text = io.readText(filePath);
    const updated = withRenames(text);
    if (updated !== text) io.writeText(filePath, updated);
  }

  for (const [file, target] of renamed) {
    if (file === target) renamed.delete(file);
  }
  return renamed;
}

function stemOf(file: string): string {
  return file.replace(SOURCE_EXTENSION, '');
}

function hashedName(io: HashPort, file: string, body: string): string {
  const extension = file.match(SOURCE_EXTENSION)?.[0] ?? '';
  const stem = stemOf(file);
  const segment = stem.match(HASH_SEGMENT);
  const slot = segment ? hashSlotOf(segment[1]!) : DEFAULT_HASH_SLOT;
  const base = segment ? stem.slice(0, -segment[0].length) : stem;
  return `${base}-${hashChunkContent(io, body, slot)}${extension}`;
}
