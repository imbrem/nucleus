import { tree } from "$lib/server/notes";
import type { LayoutServerLoad } from "./$types";

export const prerender = true;

export const load: LayoutServerLoad = () => ({ tree: tree() });
