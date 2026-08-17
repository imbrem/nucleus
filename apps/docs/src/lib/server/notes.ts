// Bridge between the repository `notes/` tree and the site.
//
// This lives under `$lib/server` so the Markdown source and `marked` stay out
// of the client bundle: pages are prerendered, so the browser only ever sees
// the rendered HTML.

import { base } from "$app/paths";

import {
  buildCorpus,
  notePath,
  renderNote,
  sourceUrl,
  type Note,
  type RenderOptions,
  type TreeEntry,
} from "../../../note-corpus.ts";

const REPOSITORY = "imbrem/nucleus";

// Vite reads the corpus at build time; `notes/` sits above the SvelteKit
// project, so the glob is relative rather than aliased.
const sources = import.meta.glob("../../../../../notes/**/*.md", {
  query: "?raw",
  import: "default",
  eager: true,
}) as Record<string, string>;

const files = Object.fromEntries(
  Object.entries(sources).map(([path, source]) => [
    path.replace(/^(\.\.\/)+/, ""),
    source,
  ]),
);

export const corpus = buildCorpus(files);

// The docs build is the enforcement point named in #569: a note that links at
// nothing, or that omits required metadata, fails `glu docs` rather than
// shipping a broken page. `notes/note-corpus.test.ts` reports the same
// problems without a full site build.
if (corpus.problems.length > 0) {
  const detail = corpus.problems
    .map((problem) => `  ${problem.path}: ${problem.message}`)
    .join("\n");
  throw new Error(`the notes corpus has unresolved problems:\n${detail}`);
}

const options: RenderOptions = {
  base,
  revision:
    __BUILD_METADATA__.dirty || __BUILD_METADATA__.commit === "unknown"
      ? "main"
      : __BUILD_METADATA__.commit,
  repository: REPOSITORY,
};

export interface Crumb {
  title: string;
  /// Absent for a directory with no index note, so the trail never links at a
  /// page that was never written.
  href?: string;
}

export interface NotePage {
  title: string;
  status: string;
  summary?: string;
  issues: string[];
  reviewed?: string;
  sourceRevision?: string;
  path: string;
  source: string;
  html: string;
  crumbs: Crumb[];
  children: TreeEntry[];
}

function descend(entries: TreeEntry[], slug: string): TreeEntry[] {
  if (slug === "") return entries;
  const segments = slug.split("/");
  let children = entries;
  for (let index = 0; index < segments.length; index += 1) {
    const prefix = segments.slice(0, index + 1).join("/");
    const entry = children.find((candidate) => candidate.slug === prefix);
    if (!entry) return [];
    children = entry.children;
  }
  return children;
}

function crumbs(note: Note): Crumb[] {
  const trail: Crumb[] = [{ title: "Notes", href: notePath("", base) }];
  if (note.slug === "") return trail;
  const segments = note.slug.split("/");
  for (const [index, segment] of segments.entries()) {
    const prefix = segments.slice(0, index + 1).join("/");
    const found = corpus.bySlug.get(prefix);
    trail.push({
      title: found?.metadata.title ?? segment,
      href: found ? notePath(prefix, base) : undefined,
    });
  }
  return trail;
}

export function notes(): Note[] {
  return corpus.notes;
}

export function tree(): TreeEntry[] {
  return corpus.tree;
}

export function page(slug: string): NotePage | undefined {
  const note = corpus.bySlug.get(slug);
  if (!note) return undefined;
  return {
    title: note.metadata.title,
    status: note.metadata.status,
    summary: note.metadata.summary,
    issues: note.metadata.issues,
    reviewed: note.metadata.reviewed,
    sourceRevision: note.metadata.sourceRevision,
    path: note.path,
    source: sourceUrl(note, options),
    html: renderNote(corpus, note, options),
    crumbs: crumbs(note),
    children: descend(corpus.tree, note.slug),
  };
}
