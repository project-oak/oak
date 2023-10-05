# Updating the Logo

- recommended software: [inkscape](https://inkscape.org/)
- might need to install `Product Sans` font

## Add a new variant of the logo

- open
  [docs/oak-logo/draft/oak-logo-overview.svg](docs/oak-logo/draft/oak-logo-overview.svg).
- copy and paste an existing variant of the logo, e.g., "Oak Containers"
- ungroup the copied logo (`ctrl + shift + g`)
- replace "Containers" with the name of the new variant
- save `oak-logo-overview.svg` with the new logo
- copy the new logo (`ctrl + c`)
- open a new file and paste the new logo
- go to `File > Document Properties > Resize to content`
- to avoid problems with missing fonts, convert the font to paths with select
  all (`ctrl + a`) and `Path > Object to Path`.
- save as `svg` to `docs/oak-logo/svgs`
- save as `png` to `docs/oak/logo` with `File > Export` and default settings
