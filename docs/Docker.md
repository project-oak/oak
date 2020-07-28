# Installing Docker

## MacOS

### From Docker.com

[Download the dmg](https://www.docker.com/get-started) and install it.

Run Docker and follow through the initial setup dialog (doesn't take long and possibly can be bypassed, but we don't know how).

It won't work until you've completed this step.

### Using Homeboew

```bash
brew install docker
```

And then what? Oak's install script fails with

```bash
Cannot connect to the Docker daemon at unix:///var/run/docker.sock. Is the docker daemon running?
```