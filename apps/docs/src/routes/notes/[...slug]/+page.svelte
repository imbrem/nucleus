<script lang="ts">
  import { base } from "$app/paths";
  import type { PageProps } from "./$types";

  let { data }: PageProps = $props();

  const issueHref = (reference: string) =>
    /^\d+$/.test(reference)
      ? `https://github.com/imbrem/nucleus/issues/${reference}`
      : reference;

  const issueLabel = (reference: string) =>
    /^\d+$/.test(reference) ? `#${reference}` : reference;
</script>

<svelte:head><title>{data.title} · Nucleus notes</title></svelte:head>

<article class="note">
  <nav class="crumbs" aria-label="Breadcrumb">
    {#each data.crumbs as crumb, index (crumb.title)}
      {#if index > 0}<span aria-hidden="true">/</span>{/if}
      {#if index === data.crumbs.length - 1}
        <span aria-current="page">{crumb.title}</span>
      {:else if crumb.href}
        <a href={crumb.href}>{crumb.title}</a>
      {:else}
        <span>{crumb.title}</span>
      {/if}
    {/each}
  </nav>

  <h1>{data.title}</h1>

  <dl class="note-metadata">
    <dt>status</dt>
    <dd><span class={`status status-${data.status}`}>{data.status}</span></dd>
    {#if data.reviewed}
      <dt>reviewed</dt>
      <dd>{data.reviewed}</dd>
    {/if}
    {#if data.sourceRevision}
      <dt>source revision</dt>
      <dd><code>{data.sourceRevision}</code></dd>
    {/if}
    {#if data.issues.length > 0}
      <dt>issues</dt>
      <dd>
        {#each data.issues as reference, index (reference)}
          {#if index > 0}<span>, </span>{/if}
          <a href={issueHref(reference)}>{issueLabel(reference)}</a>
        {/each}
      </dd>
    {/if}
    <dt>source</dt>
    <dd><a href={data.source}>{data.path}</a></dd>
  </dl>

  <div class="note-body">
    <!-- Repository Markdown rendered at build time; the corpus is trusted
         source, and the browser never sees the Markdown or the renderer. -->
    {@html data.html}
  </div>

  {#if data.children.length > 0}
    <section class="note-children">
      <h2>In this section</h2>
      <ul>
        {#each data.children as child (child.slug)}
          {#if child.status}
            <li>
              <a href={`${base}/notes/${child.slug}/`}>{child.title}</a>
              <span class={`status status-${child.status}`}>{child.status}</span
              >
              {#if child.summary}<p>{child.summary}</p>{/if}
            </li>
          {/if}
        {/each}
      </ul>
    </section>
  {/if}
</article>
