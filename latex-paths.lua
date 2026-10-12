-- Pandoc Lua filter: in LaTeX output, typeset inline code that looks like a
-- path or identifier with separators as \path{...}, which (with the url package) can
-- break across lines. Plain \texttt cannot break, so long Ragu paths such as
-- crates/ragu_pcd/src/internal/fold_revdot.rs overflow the margin.
function Code(el)
  if not FORMAT:match('latex') then
    return nil
  end
  if el.text:match('^[%w_%./:%-]+$') and el.text:find('[/_]') then
    return pandoc.RawInline('latex', '\\path{' .. el.text .. '}')
  end
  return nil
end
