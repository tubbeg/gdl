CDQ : use game.context, not protocols, and not :as gm just refer


safe-get properties => context protocol for properties
'get-property'

TODO get-texture protocol or texture-asset file ? -> use @ image, implement @assets?

=> image should anyway GET PASSED A TEXTURE-REGION ! makes it so much simpler
=> and dont need for gui -widgets e.g. create image-widget ...


lein codox doesnt' find gdl.default-context function ->Context ...
it hides such ones !


; [RED] not working with default BitmapFont and world unit scale also,
 set markup enabled & set integer positions false ?

; WIDGETS IN CONTEXT
; => !
; => super simple test widgets add to simple-test !!

; STAGE IN CONTEXT (gdl.scene2d.stage ), stage-hit? ... or mouse-over-ui-widget?

; TILEMAP

; SOUND

; INPUT

; COLORS make keywords/vectors

; TODO all context stuff ns-d keys !! at least without gui-stuff views for now...
; or just call 'create' ?
; and some are empty and just extending passing record class?

; separate gui & world-view => don't need in test
; only require what needed in test !!!
; ( remove default context !! )  (but it's a good default ! even if we dont use world-... )

remove scen2d.actor => namespace graph looks better & makes moer senes ?(ui could do it  !  / widget )

TODO
interfaces for widgets/stage/actor/tilemap/?
