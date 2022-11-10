[![](https://jitpack.io/v/damn/engine.svg)](https://jitpack.io/#damn/engine)

# engine

Minimal clojure 2D game engine for desktop.
Based on [libGDX](https://libgdx.com/).

# Graphic Features

* Colors
* Shape drawer (same batch as image renderer)
* Images
* Sprite-sheets
* Sprite-sheet font renderer
* Render text in different colors with some formatting
* Animations
* GUI and world coordinate systems / cameras
* FitViewport
* Rendering to both systems with the respective coordinate systems
* Shape drawer & image drawer understand the coordinate system
  so I can render shapes at GUI coordinates or world coordinates and it gets rendered properly
* Rendering tilemap
* Unproject mouse coordinate to GUI or world coordinates.
* Tilemap & Image tinting for lights/shadows.

# Demo

```
lein run -m engine.repl
```
