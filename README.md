<p align="center">
  <img src="https://github.com/damn/gdx/blob/main/logo.png" width="250" height="105"/>
</p>

# What is GDL?

GDL is a functional 2D game engine built around the idea of a __context__ object which holds the current state of the application.

As you can see in the hello-world example below we call `create-context` once on app start and then it gets passed every frame to the `render` function.

The context is a clojure record which implements certain protocols, as defined in [gdl.context](https://damn.github.io/gdl/gdl.context.html). 
It is available in `gdl.app/current-context` for developer debuggings and is used by the UI callback functions.

GDL is basically a clojure API over the revalant/2D parts [libgdx](https://libgdx.com/), as GDL evolved as an engine for [Cyber Dungeon Quest](https://github.com/damn/Cyber-Dungeon-Quest), an action RPG project. 
But you can easily extend the API for more libgdx features. 

At the moment the `context` needs to contain `atom`s for your state/entities and is not getting replaced by the return value of `render`. This is done because the UI-scenegraph used is still mutating objects and using callbacks which query `gdl.app/current-context`.

You have full access to all libgdx under the hood and can do direct java interop anytime or acccess the OpenGL context, etc.

__Libgdx__ supports android and ios too, but I have not used those backends yet.

## [Context API](https://damn.github.io/gdl/gdl.context.html)

* Change screens (different separate applications 'screens' like main-menu, options-menu, etc )
* Loading/setting cursors
* Having a GUI-view and a World-view (with a `world-unit-scale`, which means you can draw and reason about your game world at world-coordinates and not pixel-coordinates)
* Load and draw images
* Checking for Mouse/Key input
* Drawing geometric shapes
* Playing sounds
* [Scene graph](https://libgdx.com/wiki/graphics/2d/scene2d/scene2d) for [UI widgets](https://github.com/kotcrab/vis-ui)
* Loading truetype fonts & drawing text
* Loading [tiled](https://www.mapeditor.org/) `.tmx` maps and drawing them with lights&shadows in `world-unit-scale`

# Hello World

You can run the hello world example in this repository with:

```
lein run -m gdl.hello-world
```

https://github.com/damn/gdl/blob/f34a451e559363a1876e9d386516108333bdc5ce/test/gdl/hello_world.clj#L1-L25

# On Mac

You need to set this environment variable:

```
export JVM_OPTS=-XstartOnFirstThread
```

# Extending the `Context` for your game

In [Cyber Dungeon Quest](https://github.com/damn/Cyber-Dungeon-Quest) I have defined more [game-specific context protocols](https://github.com/damn/Cyber-Dungeon-Quest/blob/master/src/cdq/context.clj). 

There is an example in [context.mouseover-entity](https://github.com/damn/Cyber-Dungeon-Quest/blob/master/src/context/mouseover_entity.clj) how to extend the context with your own protocols. 

Basically you call `extend-type gdl.context.Context` with your protocols and merge the necessary context-data at app start with the existing default-context.

By using namespaced keywords like `:context/mouseover-entity` and clojure's map destructuring it becomes quite __simple&easy__ to manage all the data in one object.

The context returned by `render` will NOT update the original context. I am using `atoms` for my game entities, so it's not just one huge map but can use 


# Installation

[![](https://jitpack.io/v/damn/gdl.svg)](https://jitpack.io/#damn/gdl)

Add the following to your project.clj file:

```clojure
:repositories [["jitpack" "https://jitpack.io"]]

:dependencies [[com.github.damn/gdl "main-SNAPSHOT"]]
```

# [API Documentation](https://damn.github.io/gdl/)

# Games made with GDL

* [Cyber Dungeon Quest](https://github.com/damn/Cyber-Dungeon-Quest)
