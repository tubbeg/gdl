<p align="center">
  <img src="https://github.com/damn/gdx/blob/main/resources/logo.png"/>
</p>

[![](https://jitpack.io/v/damn/gdx.svg)](https://jitpack.io/#damn/gdx)

# gdx - game development extension

Based on [libGDX](https://libgdx.com/).

Supporting desktop backend and 2D graphics API only at the moment.

Feedback appreciated.

This library is the backend for a roguelike action RPG game I am developing.
I thought it may be useful to someone else too.

# How to use

Leiningen: Add to project.clj:
```
:repositories [["jitpack" "https://jitpack.io"]]
```

```
:dependencies [[com.github.damn/gdx "1.0"]]
```

# Hello world window

```
(ns hello-world.core
  (:require [gdx.app :as app]
            [gdx.game :as game]))

(game/defscreen main-screen
  :show (fn [])
  :render (fn [])
  :update (fn [delta])
  :destroy (fn []))

(defn app []
  (app/create (game/create {:main main-screen})
              {:title "Hello World!"
               :width 800
               :height 600
               :full-screen false}))

(defn -main []
  (app))

```
