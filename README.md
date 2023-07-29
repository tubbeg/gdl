<p align="left">
  <img src="https://github.com/damn/gdx/blob/main/logo.png" width="250" height="105"/>
</p>

#  Details

Based on [libGDX](https://libgdx.com/).

Supporting desktop backend and 2D graphics API only at the moment.

Feedback appreciated.

This library is the backend for a roguelike action RPG game I am developing.

# Installation

[![](https://jitpack.io/v/damn/gdx.svg)](https://jitpack.io/#damn/gdx)

Add the following to your project.clj file:

```
:repositories [["jitpack" "https://jitpack.io"]]

:dependencies [[com.github.damn/gdx "1.0"]]
```

# Documentation

* [API docs](https://damn.github.io/gdl/)

# Hello world window

```clojure
(ns hello-world.core
  (:require [gdx.app :as app]
            [gdx.game :as game]
            [gdx.graphics :as g]))

(def main-screen
  {:show (fn [])
   :render (fn [] (g/render-gui ; takes care of all graphics context initializations
                    (fn []
                      ;; your render code here
                      )))
   :update (fn [delta] ; delta is elapsed time in ms since last update
            ;; your update code here
            )
   :destroy (fn [])})

(defn app []
  (app/create (game/create {:main main-screen})
              {:title "Hello World!"
               :width 800
               :height 600
               :full-screen false}))

(defn -main []
  (app))

```
