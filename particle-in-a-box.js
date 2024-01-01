(function(){
    const canvas = document.getElementById('particleCanvas');
    const ctx = canvas.getContext('2d');

    // Parameters
    const numParticles = 250;
    const particles = [];
    const particleSize = 10; // radius of the particle
    const speedFactor = 10;
    
    const depth = 1000; // The range for the z-axis

    // Define a Particle class
    class Particle {
        constructor() {
            // Random position within the canvas, accounting for particle size
            this.x = Math.random() * canvas.width;
            this.y = Math.random() * canvas.height;
            this.z = Math.random() * depth;
            // Random velocity
            this.vx = speedFactor * (Math.random() - 0.5);
            this.vy = speedFactor * (Math.random() - 0.5);
            this.vz = speedFactor * (Math.random() - 0.5);

            this.r = Math.random() * 255;
            this.g = Math.random() * 255;
            this.b = Math.random() * 255;

            // Set the initial color
            this.setColor();
        }

        setColor() {
            // Adjust the color transparency based on the z-depth
            const alpha = 1 - (this.z / depth);
            this.color = `rgba(${this.r}, ${this.g}, ${this.b}, ${alpha})`;
        }
    
        update() {
            // Update position with velocity
            this.x += this.vx;
            this.y += this.vy;
            this.z += this.vz;
    
            // Reflect off the walls
            if (this.x <= particleSize || this.x >= canvas.width - particleSize) this.vx *= -1;
            if (this.y <= particleSize || this.y >= canvas.height - particleSize) this.vy *= -1;
            if (this.z <= 0 || this.z >= depth) this.vz *= -1;

            this.setColor(); // Update color based on new position
        }
    
        draw() {
            ctx.beginPath();
            // Scale size based on z-position to simulate perspective
            let size = particleSize * ((depth - this.z) / depth);
            size = Math.max(0.1, size); // Ensure size is never negative, but at least 0.1
            ctx.arc(this.x, this.y, size, 0, 2 * Math.PI);
            ctx.fillStyle = this.color; // Use the particle's color
            ctx.fill();
        }
    }
    
    function resizeCanvas() {
        canvas.width = 640;
        canvas.height = 360;
    }
    
    // Animation function
    function animate() {
        ctx.clearRect(0, 0, canvas.width, canvas.height); // Clear canvas
        ctx.fillStyle = "black";
        ctx.fillRect(0, 0, canvas.width, canvas.height); // Fill canvas with black
        for (const particle of particles) {
            particle.update(); // Update particle position
            particle.draw();   // Draw particle
        }
        requestAnimationFrame(animate); // Call animate again
    }
    
    // Start the animation
    window.addEventListener('resize', resizeCanvas, false);
    resizeCanvas();

    // Initialize particles
    for (let i = 0; i < numParticles; i++) {
        particles.push(new Particle());
    }
    
    animate();
})();