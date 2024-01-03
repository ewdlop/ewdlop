(function() {
    gsap.to(".green", {rotation: 360, x: 100, duration: 1});

    // target the element with a class of "purple" - rotate and move FROM 100px to the left over the course of 1 second. 
    gsap.from(".purple", {rotation: -360, x: -100, duration: 1});
    
    // target the element with a class of "blue" - rotate and move FROM 100px to the left, TO 100px to the right over the course of 1 second. 
    gsap.fromTo(".blue", {x: window.innerWidth/2},{rotation: 360, x: 100, duration: 1});
})();