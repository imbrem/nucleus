import { error } from "@sveltejs/kit";

import { notes, page } from "$lib/server/notes";
import type { EntryGenerator, PageServerLoad } from "./$types";

export const prerender = true;

// The corpus is the only source of routes, so a note appears on the site as
// soon as its Markdown lands under `notes/`.
export const entries: EntryGenerator = () =>
  notes().map((note) => ({ slug: note.slug }));

export const load: PageServerLoad = ({ params }) => {
  // `trailingSlash: "always"` leaves the slash on the rest parameter, so
  // `/notes/architecture/status/` arrives as `architecture/status/`.
  const slug = params.slug.replace(/\/+$/, "");
  const found = page(slug);
  if (!found) error(404, `no note at notes/${slug}`);
  return found;
};
